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
                (uu___92_952.FStar_TypeChecker_Env.erasable_types_tab)
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
      match u.FStar_Syntax_Syntax.ctx_uvar_meta with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
          a) ->
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
      | uu____2313 -> false
  
let (defer_maybe_tac_lit :
  Prims.string ->
    FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem ->
      worklist -> worklist)
  =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        match prob.FStar_TypeChecker_Common.relation with
        | FStar_TypeChecker_Common.EQ  ->
            let should_defer_tac t =
              let uu____2351 = FStar_Syntax_Util.head_and_args t  in
              match uu____2351 with
              | (head1,uu____2375) ->
                  let uu____2400 =
                    let uu____2401 = FStar_Syntax_Subst.compress head1  in
                    uu____2401.FStar_Syntax_Syntax.n  in
                  (match uu____2400 with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____2411) ->
                       let uu____2428 =
                         should_defer_uvar_to_user_tac wl.tcenv uv  in
                       (uu____2428, (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                   | uu____2432 -> (false, ""))
               in
            let uu____2437 =
              should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
            (match uu____2437 with
             | (l1,r1) ->
                 let uu____2450 =
                   should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                 (match uu____2450 with
                  | (l2,r2) ->
                      if l1 || l2
                      then
                        let uu___314_2464 = wl  in
                        let uu____2465 =
                          let uu____2475 =
                            let uu____2483 =
                              FStar_Thunk.mkv
                                (Prims.op_Hat r1 (Prims.op_Hat ", " r2))
                               in
                            ((wl.ctr), uu____2483,
                              (FStar_TypeChecker_Common.TProb prob))
                             in
                          uu____2475 :: (wl.wl_deferred_to_tac)  in
                        {
                          attempting = (uu___314_2464.attempting);
                          wl_deferred = (uu___314_2464.wl_deferred);
                          wl_deferred_to_tac = uu____2465;
                          ctr = (uu___314_2464.ctr);
                          defer_ok = (uu___314_2464.defer_ok);
                          smt_ok = (uu___314_2464.smt_ok);
                          umax_heuristic_ok =
                            (uu___314_2464.umax_heuristic_ok);
                          tcenv = (uu___314_2464.tcenv);
                          wl_implicits = (uu___314_2464.wl_implicits)
                        }
                      else
                        defer_lit reason
                          (FStar_TypeChecker_Common.TProb prob) wl))
        | uu____2496 ->
            defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___320_2514 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___320_2514.wl_deferred);
         wl_deferred_to_tac = (uu___320_2514.wl_deferred_to_tac);
         ctr = (uu___320_2514.ctr);
         defer_ok = (uu___320_2514.defer_ok);
         smt_ok = (uu___320_2514.smt_ok);
         umax_heuristic_ok = (uu___320_2514.umax_heuristic_ok);
         tcenv = (uu___320_2514.tcenv);
         wl_implicits = (uu___320_2514.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____2528 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2528 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2562 = FStar_Syntax_Util.type_u ()  in
            match uu____2562 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2574 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2574 with
                 | (uu____2586,tt,wl1) ->
                     let uu____2589 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2589, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2595  ->
    match uu___14_2595 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2601  -> FStar_TypeChecker_Common.TProb _2601) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2607  -> FStar_TypeChecker_Common.CProb _2607) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2615 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2615 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2635  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2677 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2677 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2677 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2677 FStar_TypeChecker_Common.problem *
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
                        let uu____2764 =
                          let uu____2773 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2773]  in
                        FStar_List.append scope uu____2764
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2816 =
                      let uu____2819 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2819  in
                    FStar_List.append uu____2816
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2838 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2838 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2858 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2858;
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
                  (let uu____2932 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2932 with
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
                  (let uu____3020 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____3020 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____3058 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____3058 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____3058 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____3058 FStar_TypeChecker_Common.problem *
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
                          let uu____3126 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3126]  in
                        let uu____3145 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____3145
                     in
                  let uu____3148 =
                    let uu____3155 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___403_3166 = wl  in
                       {
                         attempting = (uu___403_3166.attempting);
                         wl_deferred = (uu___403_3166.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___403_3166.wl_deferred_to_tac);
                         ctr = (uu___403_3166.ctr);
                         defer_ok = (uu___403_3166.defer_ok);
                         smt_ok = (uu___403_3166.smt_ok);
                         umax_heuristic_ok =
                           (uu___403_3166.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___403_3166.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____3155
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____3148 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3178 =
                              let uu____3183 =
                                let uu____3184 =
                                  let uu____3193 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____3193
                                   in
                                [uu____3184]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____3183  in
                            uu____3178 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____3221 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3221;
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
                let uu____3269 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3269;
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
  'Auu____3284 .
    worklist ->
      'Auu____3284 FStar_TypeChecker_Common.problem ->
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
              let uu____3317 =
                let uu____3320 =
                  let uu____3321 =
                    let uu____3328 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3328)  in
                  FStar_Syntax_Syntax.NT uu____3321  in
                [uu____3320]  in
              FStar_Syntax_Subst.subst uu____3317 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3350 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3350
        then
          let uu____3358 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3361 = prob_to_string env d  in
          let uu____3363 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3370 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3358 uu____3361 uu____3363 uu____3370
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3382 -> failwith "impossible"  in
           let uu____3385 =
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
           match uu____3385 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3428  ->
            match uu___15_3428 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3440 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3444 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3444 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3475  ->
           match uu___16_3475 with
           | UNIV uu____3478 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3485 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3485
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
        (fun uu___17_3513  ->
           match uu___17_3513 with
           | UNIV (u',t) ->
               let uu____3518 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3518
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3525 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3537 =
        let uu____3538 =
          let uu____3539 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3539
           in
        FStar_Syntax_Subst.compress uu____3538  in
      FStar_All.pipe_right uu____3537 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3551 =
        let uu____3552 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3552  in
      FStar_All.pipe_right uu____3551 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3564 =
        let uu____3568 =
          let uu____3570 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3570  in
        FStar_Pervasives_Native.Some uu____3568  in
      FStar_Profiling.profile (fun uu____3573  -> sn' env t) uu____3564
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
          let uu____3598 =
            let uu____3602 =
              let uu____3604 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3604  in
            FStar_Pervasives_Native.Some uu____3602  in
          FStar_Profiling.profile
            (fun uu____3607  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3598
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3615 = FStar_Syntax_Util.head_and_args t  in
    match uu____3615 with
    | (h,uu____3634) ->
        let uu____3659 =
          let uu____3660 = FStar_Syntax_Subst.compress h  in
          uu____3660.FStar_Syntax_Syntax.n  in
        (match uu____3659 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3665 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3678 =
        let uu____3682 =
          let uu____3684 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3684  in
        FStar_Pervasives_Native.Some uu____3682  in
      FStar_Profiling.profile
        (fun uu____3689  ->
           let uu____3690 = should_strongly_reduce t  in
           if uu____3690
           then
             let uu____3693 =
               let uu____3694 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3694  in
             FStar_All.pipe_right uu____3693 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3678 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3705 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3705) ->
        (FStar_Syntax_Syntax.term * 'Auu____3705)
  =
  fun env  ->
    fun t  ->
      let uu____3728 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3728, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3780  ->
              match uu____3780 with
              | (x,imp) ->
                  let uu____3799 =
                    let uu___509_3800 = x  in
                    let uu____3801 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___509_3800.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___509_3800.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3801
                    }  in
                  (uu____3799, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3825 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3825
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3829 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3829
        | uu____3832 -> u2  in
      let uu____3833 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3833
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3850 =
          let uu____3854 =
            let uu____3856 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3856  in
          FStar_Pervasives_Native.Some uu____3854  in
        FStar_Profiling.profile
          (fun uu____3859  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3850 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3981 = norm_refinement env t12  in
                 match uu____3981 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3996;
                     FStar_Syntax_Syntax.vars = uu____3997;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____4021 =
                       let uu____4023 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____4025 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____4023 uu____4025
                        in
                     failwith uu____4021)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____4041 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____4041
          | FStar_Syntax_Syntax.Tm_uinst uu____4042 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4079 =
                   let uu____4080 = FStar_Syntax_Subst.compress t1'  in
                   uu____4080.FStar_Syntax_Syntax.n  in
                 match uu____4079 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4095 -> aux true t1'
                 | uu____4103 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____4118 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4149 =
                   let uu____4150 = FStar_Syntax_Subst.compress t1'  in
                   uu____4150.FStar_Syntax_Syntax.n  in
                 match uu____4149 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4165 -> aux true t1'
                 | uu____4173 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4188 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4235 =
                   let uu____4236 = FStar_Syntax_Subst.compress t1'  in
                   uu____4236.FStar_Syntax_Syntax.n  in
                 match uu____4235 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4251 -> aux true t1'
                 | uu____4259 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4274 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4289 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4304 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4319 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4334 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4363 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4396 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4417 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4444 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4472 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4509 ->
              let uu____4516 =
                let uu____4518 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4520 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4518 uu____4520
                 in
              failwith uu____4516
          | FStar_Syntax_Syntax.Tm_ascribed uu____4535 ->
              let uu____4562 =
                let uu____4564 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4566 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4564 uu____4566
                 in
              failwith uu____4562
          | FStar_Syntax_Syntax.Tm_delayed uu____4581 ->
              let uu____4596 =
                let uu____4598 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4600 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4598 uu____4600
                 in
              failwith uu____4596
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4615 =
                let uu____4617 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4619 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4617 uu____4619
                 in
              failwith uu____4615
           in
        let uu____4634 = whnf env t1  in aux false uu____4634
  
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
      let uu____4679 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4679 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4720 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4720, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4747 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4747 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4807  ->
    match uu____4807 with
    | (t_base,refopt) ->
        let uu____4838 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4838 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4880 =
      let uu____4884 =
        let uu____4887 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4912  ->
                  match uu____4912 with | (uu____4920,uu____4921,x) -> x))
           in
        FStar_List.append wl.attempting uu____4887  in
      FStar_List.map (wl_prob_to_string wl) uu____4884  in
    FStar_All.pipe_right uu____4880 (FStar_String.concat "\n\t")
  
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
  fun uu____4981  ->
    match uu____4981 with
    | Flex (uu____4983,u,uu____4985) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4992  ->
    match uu____4992 with
    | Flex (uu____4994,c,args) ->
        let uu____4997 = print_ctx_uvar c  in
        let uu____4999 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4997 uu____4999
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5009 = FStar_Syntax_Util.head_and_args t  in
    match uu____5009 with
    | (head1,_args) ->
        let uu____5053 =
          let uu____5054 = FStar_Syntax_Subst.compress head1  in
          uu____5054.FStar_Syntax_Syntax.n  in
        (match uu____5053 with
         | FStar_Syntax_Syntax.Tm_uvar uu____5058 -> true
         | uu____5072 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____5080 = FStar_Syntax_Util.head_and_args t  in
    match uu____5080 with
    | (head1,_args) ->
        let uu____5123 =
          let uu____5124 = FStar_Syntax_Subst.compress head1  in
          uu____5124.FStar_Syntax_Syntax.n  in
        (match uu____5123 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____5128) -> u
         | uu____5145 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____5170 = FStar_Syntax_Util.head_and_args t  in
      match uu____5170 with
      | (head1,args) ->
          let uu____5217 =
            let uu____5218 = FStar_Syntax_Subst.compress head1  in
            uu____5218.FStar_Syntax_Syntax.n  in
          (match uu____5217 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5226)) ->
               ((Flex (t, uv, args)), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5259 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_5284  ->
                         match uu___18_5284 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____5289 =
                               let uu____5290 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____5290.FStar_Syntax_Syntax.n  in
                             (match uu____5289 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____5295 -> false)
                         | uu____5297 -> true))
                  in
               (match uu____5259 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____5322 =
                        FStar_List.collect
                          (fun uu___19_5334  ->
                             match uu___19_5334 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____5338 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____5338]
                             | uu____5339 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____5322 FStar_List.rev  in
                    let uu____5362 =
                      let uu____5369 =
                        let uu____5378 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_5400  ->
                                  match uu___20_5400 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____5404 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____5404]
                                  | uu____5405 -> []))
                           in
                        FStar_All.pipe_right uu____5378 FStar_List.rev  in
                      let uu____5428 =
                        let uu____5431 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____5431  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____5369 uu____5428
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____5362 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____5467  ->
                                match uu____5467 with
                                | (x,i) ->
                                    let uu____5486 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____5486, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____5517  ->
                                match uu____5517 with
                                | (a,i) ->
                                    let uu____5536 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____5536, i)) args_sol
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
           | uu____5558 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5580 =
          let uu____5603 =
            let uu____5604 = FStar_Syntax_Subst.compress k  in
            uu____5604.FStar_Syntax_Syntax.n  in
          match uu____5603 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5686 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5686)
              else
                (let uu____5721 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5721 with
                 | (ys',t1,uu____5754) ->
                     let uu____5759 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5759))
          | uu____5798 ->
              let uu____5799 =
                let uu____5804 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5804)  in
              ((ys, t), uu____5799)
           in
        match uu____5580 with
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
                 let uu____5899 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5899 c  in
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
               (let uu____5977 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5977
                then
                  let uu____5982 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5984 = print_ctx_uvar uv  in
                  let uu____5986 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5982 uu____5984 uu____5986
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5995 =
                   let uu____5997 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5997  in
                 let uu____6000 =
                   let uu____6003 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____6003
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5995 uu____6000 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____6036 =
               let uu____6037 =
                 let uu____6039 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____6041 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____6039 uu____6041
                  in
               failwith uu____6037  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____6107  ->
                       match uu____6107 with
                       | (a,i) ->
                           let uu____6128 =
                             let uu____6129 = FStar_Syntax_Subst.compress a
                                in
                             uu____6129.FStar_Syntax_Syntax.n  in
                           (match uu____6128 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____6155 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____6165 =
                 let uu____6167 = is_flex g  in Prims.op_Negation uu____6167
                  in
               if uu____6165
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____6176 = destruct_flex_t g wl  in
                  match uu____6176 with
                  | (Flex (uu____6181,uv1,args),wl1) ->
                      ((let uu____6186 = args_as_binders args  in
                        assign_solution uu____6186 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___771_6188 = wl1  in
              {
                attempting = (uu___771_6188.attempting);
                wl_deferred = (uu___771_6188.wl_deferred);
                wl_deferred_to_tac = (uu___771_6188.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___771_6188.defer_ok);
                smt_ok = (uu___771_6188.smt_ok);
                umax_heuristic_ok = (uu___771_6188.umax_heuristic_ok);
                tcenv = (uu___771_6188.tcenv);
                wl_implicits = (uu___771_6188.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6213 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6213
         then
           let uu____6218 = FStar_Util.string_of_int pid  in
           let uu____6220 =
             let uu____6222 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____6222 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6218 uu____6220
         else ());
        commit sol;
        (let uu___779_6236 = wl  in
         {
           attempting = (uu___779_6236.attempting);
           wl_deferred = (uu___779_6236.wl_deferred);
           wl_deferred_to_tac = (uu___779_6236.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___779_6236.defer_ok);
           smt_ok = (uu___779_6236.smt_ok);
           umax_heuristic_ok = (uu___779_6236.umax_heuristic_ok);
           tcenv = (uu___779_6236.tcenv);
           wl_implicits = (uu___779_6236.wl_implicits)
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
          (let uu____6272 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6272
           then
             let uu____6277 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6281 =
               let uu____6283 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____6283 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6277 uu____6281
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
        let uu____6318 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6318 FStar_Util.set_elements  in
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
      let uu____6358 = occurs uk t  in
      match uu____6358 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6397 =
                 let uu____6399 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6401 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6399 uu____6401
                  in
               FStar_Pervasives_Native.Some uu____6397)
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
            let uu____6521 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6521 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6572 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6629  ->
             match uu____6629 with
             | (x,uu____6641) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6659 = FStar_List.last bs  in
      match uu____6659 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6683) ->
          let uu____6694 =
            FStar_Util.prefix_until
              (fun uu___21_6709  ->
                 match uu___21_6709 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6712 -> false) g
             in
          (match uu____6694 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6726,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6763 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6763 with
        | (pfx,uu____6773) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6785 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6785 with
             | (uu____6793,src',wl1) ->
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
                 | uu____6907 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6908 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6972  ->
                  fun uu____6973  ->
                    match (uu____6972, uu____6973) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____7076 =
                          let uu____7078 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____7078
                           in
                        if uu____7076
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____7112 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____7112
                           then
                             let uu____7129 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____7129)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6908 with | (isect,uu____7179) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____7215 'Auu____7216 .
    (FStar_Syntax_Syntax.bv * 'Auu____7215) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____7216) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7274  ->
              fun uu____7275  ->
                match (uu____7274, uu____7275) with
                | ((a,uu____7294),(b,uu____7296)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____7312 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____7312) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7343  ->
           match uu____7343 with
           | (y,uu____7350) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____7360 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____7360) Prims.list ->
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
                   let uu____7522 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7522
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7555 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7607 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7651 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7672 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7680  ->
    match uu___22_7680 with
    | MisMatch (d1,d2) ->
        let uu____7692 =
          let uu____7694 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7696 =
            let uu____7698 =
              let uu____7700 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7700 ")"  in
            Prims.op_Hat ") (" uu____7698  in
          Prims.op_Hat uu____7694 uu____7696  in
        Prims.op_Hat "MisMatch (" uu____7692
    | HeadMatch u ->
        let uu____7707 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7707
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7716  ->
    match uu___23_7716 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7733 -> HeadMatch false
  
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
          let uu____7755 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7755 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7766 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7790 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7800 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7819 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7819
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7820 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7821 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7822 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7835 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7849 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7873) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7879,uu____7880) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7922) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7947;
             FStar_Syntax_Syntax.index = uu____7948;
             FStar_Syntax_Syntax.sort = t2;_},uu____7950)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7958 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7959 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7960 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7975 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7982 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8002 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____8002
  
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
           { FStar_Syntax_Syntax.blob = uu____8021;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____8022;
             FStar_Syntax_Syntax.ltyp = uu____8023;
             FStar_Syntax_Syntax.rng = uu____8024;_},uu____8025)
            ->
            let uu____8036 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____8036 t21
        | (uu____8037,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____8038;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____8039;
             FStar_Syntax_Syntax.ltyp = uu____8040;
             FStar_Syntax_Syntax.rng = uu____8041;_})
            ->
            let uu____8052 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____8052
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____8064 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____8064
            then FullMatch
            else
              (let uu____8069 =
                 let uu____8078 =
                   let uu____8081 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____8081  in
                 let uu____8082 =
                   let uu____8085 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____8085  in
                 (uu____8078, uu____8082)  in
               MisMatch uu____8069)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____8091),FStar_Syntax_Syntax.Tm_uinst (g,uu____8093)) ->
            let uu____8102 = head_matches env f g  in
            FStar_All.pipe_right uu____8102 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____8103) -> HeadMatch true
        | (uu____8105,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8109 = FStar_Const.eq_const c d  in
            if uu____8109
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____8119),FStar_Syntax_Syntax.Tm_uvar (uv',uu____8121)) ->
            let uu____8154 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____8154
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____8164),FStar_Syntax_Syntax.Tm_refine (y,uu____8166)) ->
            let uu____8175 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8175 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8177),uu____8178) ->
            let uu____8183 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8183 head_match
        | (uu____8184,FStar_Syntax_Syntax.Tm_refine (x,uu____8186)) ->
            let uu____8191 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8191 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8192,FStar_Syntax_Syntax.Tm_type
           uu____8193) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8195,FStar_Syntax_Syntax.Tm_arrow uu____8196) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____8227),FStar_Syntax_Syntax.Tm_app (head',uu____8229))
            ->
            let uu____8278 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____8278 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____8280),uu____8281) ->
            let uu____8306 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____8306 head_match
        | (uu____8307,FStar_Syntax_Syntax.Tm_app (head1,uu____8309)) ->
            let uu____8334 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____8334 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8335,FStar_Syntax_Syntax.Tm_let
           uu____8336) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8364,FStar_Syntax_Syntax.Tm_match uu____8365) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8411,FStar_Syntax_Syntax.Tm_abs
           uu____8412) -> HeadMatch true
        | uu____8450 ->
            let uu____8455 =
              let uu____8464 = delta_depth_of_term env t11  in
              let uu____8467 = delta_depth_of_term env t21  in
              (uu____8464, uu____8467)  in
            MisMatch uu____8455
  
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
              let uu____8536 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8536  in
            (let uu____8538 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8538
             then
               let uu____8543 = FStar_Syntax_Print.term_to_string t  in
               let uu____8545 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8543 uu____8545
             else ());
            (let uu____8550 =
               let uu____8551 = FStar_Syntax_Util.un_uinst head1  in
               uu____8551.FStar_Syntax_Syntax.n  in
             match uu____8550 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8557 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8557 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8571 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8571
                        then
                          let uu____8576 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8576
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8581 ->
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
                      let uu____8599 =
                        let uu____8601 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8601 = FStar_Syntax_Util.Equal  in
                      if uu____8599
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8608 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8608
                          then
                            let uu____8613 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8615 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8613
                              uu____8615
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8620 -> FStar_Pervasives_Native.None)
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
            (let uu____8772 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8772
             then
               let uu____8777 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8779 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8781 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8777
                 uu____8779 uu____8781
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8809 =
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
               match uu____8809 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8857 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8857 with
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
                  uu____8895),uu____8896)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8917 =
                      let uu____8926 = maybe_inline t11  in
                      let uu____8929 = maybe_inline t21  in
                      (uu____8926, uu____8929)  in
                    match uu____8917 with
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
                 (uu____8972,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8973))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8994 =
                      let uu____9003 = maybe_inline t11  in
                      let uu____9006 = maybe_inline t21  in
                      (uu____9003, uu____9006)  in
                    match uu____8994 with
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
             | MisMatch uu____9061 -> fail1 n_delta r t11 t21
             | uu____9070 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____9085 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____9085
           then
             let uu____9090 = FStar_Syntax_Print.term_to_string t1  in
             let uu____9092 = FStar_Syntax_Print.term_to_string t2  in
             let uu____9094 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____9102 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9119 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____9119
                    (fun uu____9154  ->
                       match uu____9154 with
                       | (t11,t21) ->
                           let uu____9162 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____9164 =
                             let uu____9166 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____9166  in
                           Prims.op_Hat uu____9162 uu____9164))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____9090 uu____9092 uu____9094 uu____9102
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9183 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9183 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_9198  ->
    match uu___24_9198 with
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
      let uu___1268_9247 = p  in
      let uu____9250 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9251 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1268_9247.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9250;
        FStar_TypeChecker_Common.relation =
          (uu___1268_9247.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9251;
        FStar_TypeChecker_Common.element =
          (uu___1268_9247.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1268_9247.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1268_9247.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1268_9247.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1268_9247.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1268_9247.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9266 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9266
            (fun _9271  -> FStar_TypeChecker_Common.TProb _9271)
      | FStar_TypeChecker_Common.CProb uu____9272 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9295 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9295 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9303 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9303 with
           | (lh,lhs_args) ->
               let uu____9350 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9350 with
                | (rh,rhs_args) ->
                    let uu____9397 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9410,FStar_Syntax_Syntax.Tm_uvar uu____9411)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9500 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9527,uu____9528)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9543,FStar_Syntax_Syntax.Tm_uvar uu____9544)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9559,FStar_Syntax_Syntax.Tm_arrow uu____9560)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1319_9590 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1319_9590.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1319_9590.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1319_9590.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1319_9590.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1319_9590.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1319_9590.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1319_9590.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1319_9590.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1319_9590.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9593,FStar_Syntax_Syntax.Tm_type uu____9594)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1319_9610 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1319_9610.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1319_9610.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1319_9610.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1319_9610.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1319_9610.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1319_9610.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1319_9610.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1319_9610.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1319_9610.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9613,FStar_Syntax_Syntax.Tm_uvar uu____9614)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1319_9630 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1319_9630.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1319_9630.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1319_9630.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1319_9630.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1319_9630.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1319_9630.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1319_9630.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1319_9630.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1319_9630.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9633,FStar_Syntax_Syntax.Tm_uvar uu____9634)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9649,uu____9650)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9665,FStar_Syntax_Syntax.Tm_uvar uu____9666)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9681,uu____9682) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9397 with
                     | (rank,tp1) ->
                         let uu____9695 =
                           FStar_All.pipe_right
                             (let uu___1339_9699 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1339_9699.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1339_9699.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1339_9699.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1339_9699.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1339_9699.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1339_9699.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1339_9699.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1339_9699.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1339_9699.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9702  ->
                                FStar_TypeChecker_Common.TProb _9702)
                            in
                         (rank, uu____9695))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9706 =
            FStar_All.pipe_right
              (let uu___1343_9710 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1343_9710.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1343_9710.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1343_9710.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1343_9710.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1343_9710.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1343_9710.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1343_9710.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1343_9710.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1343_9710.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9713  -> FStar_TypeChecker_Common.CProb _9713)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9706)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9773 probs =
      match uu____9773 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9854 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9875 = rank wl.tcenv hd1  in
               (match uu____9875 with
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
                      (let uu____9936 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9941 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9941)
                          in
                       if uu____9936
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
          let uu____10014 = FStar_Syntax_Util.head_and_args t  in
          match uu____10014 with
          | (hd1,uu____10033) ->
              let uu____10058 =
                let uu____10059 = FStar_Syntax_Subst.compress hd1  in
                uu____10059.FStar_Syntax_Syntax.n  in
              (match uu____10058 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____10064) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____10099  ->
                           match uu____10099 with
                           | (y,uu____10108) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10131  ->
                                       match uu____10131 with
                                       | (x,uu____10140) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10145 -> false)
           in
        let uu____10147 = rank tcenv p  in
        match uu____10147 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10156 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10237 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10256 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10275 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10292 = FStar_Thunk.mkv s  in UFailed uu____10292 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10307 = FStar_Thunk.mk s  in UFailed uu____10307 
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
                        let uu____10359 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10359 with
                        | (k,uu____10367) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10380 -> false)))
            | uu____10382 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10434 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____10442 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____10442 = Prims.int_zero))
                           in
                        if uu____10434 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____10463 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____10471 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____10471 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____10463)
               in
            let uu____10475 = filter1 u12  in
            let uu____10478 = filter1 u22  in (uu____10475, uu____10478)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10513 = filter_out_common_univs us1 us2  in
                   (match uu____10513 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10573 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10573 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10576 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10593  ->
                               let uu____10594 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10596 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10594 uu____10596))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10622 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10622 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10648 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10648 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10651 ->
                   ufailed_thunk
                     (fun uu____10662  ->
                        let uu____10663 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10665 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10663 uu____10665 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10668,uu____10669) ->
              let uu____10671 =
                let uu____10673 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10675 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10673 uu____10675
                 in
              failwith uu____10671
          | (FStar_Syntax_Syntax.U_unknown ,uu____10678) ->
              let uu____10679 =
                let uu____10681 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10683 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10681 uu____10683
                 in
              failwith uu____10679
          | (uu____10686,FStar_Syntax_Syntax.U_bvar uu____10687) ->
              let uu____10689 =
                let uu____10691 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10693 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10691 uu____10693
                 in
              failwith uu____10689
          | (uu____10696,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10697 =
                let uu____10699 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10701 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10699 uu____10701
                 in
              failwith uu____10697
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10731 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10731
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10748 = occurs_univ v1 u3  in
              if uu____10748
              then
                let uu____10751 =
                  let uu____10753 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10755 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10753 uu____10755
                   in
                try_umax_components u11 u21 uu____10751
              else
                (let uu____10760 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10760)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10772 = occurs_univ v1 u3  in
              if uu____10772
              then
                let uu____10775 =
                  let uu____10777 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10779 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10777 uu____10779
                   in
                try_umax_components u11 u21 uu____10775
              else
                (let uu____10784 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10784)
          | (FStar_Syntax_Syntax.U_max uu____10785,uu____10786) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10794 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10794
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10800,FStar_Syntax_Syntax.U_max uu____10801) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10809 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10809
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10815,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10817,FStar_Syntax_Syntax.U_name uu____10818) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10820) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10822) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10824,FStar_Syntax_Syntax.U_succ uu____10825) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10827,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10934 = bc1  in
      match uu____10934 with
      | (bs1,mk_cod1) ->
          let uu____10978 = bc2  in
          (match uu____10978 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____11089 = aux xs ys  in
                     (match uu____11089 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11172 =
                       let uu____11179 = mk_cod1 xs  in ([], uu____11179)  in
                     let uu____11182 =
                       let uu____11189 = mk_cod2 ys  in ([], uu____11189)  in
                     (uu____11172, uu____11182)
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
                  let uu____11258 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11258 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11261 =
                    let uu____11262 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11262 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11261
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11267 = has_type_guard t1 t2  in (uu____11267, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11268 = has_type_guard t2 t1  in (uu____11268, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___25_11275  ->
    match uu___25_11275 with
    | Flex (uu____11277,uu____11278,[]) -> true
    | uu____11288 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11302 = f  in
      match uu____11302 with
      | Flex (uu____11304,u,uu____11306) ->
          should_defer_uvar_to_user_tac wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11330 = f  in
      match uu____11330 with
      | Flex
          (uu____11337,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11338;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11339;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11342;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11343;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11344;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11345;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11409  ->
                 match uu____11409 with
                 | (y,uu____11418) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11572 =
                  let uu____11587 =
                    let uu____11590 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11590  in
                  ((FStar_List.rev pat_binders), uu____11587)  in
                FStar_Pervasives_Native.Some uu____11572
            | (uu____11623,[]) ->
                let uu____11654 =
                  let uu____11669 =
                    let uu____11672 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11672  in
                  ((FStar_List.rev pat_binders), uu____11669)  in
                FStar_Pervasives_Native.Some uu____11654
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11763 =
                  let uu____11764 = FStar_Syntax_Subst.compress a  in
                  uu____11764.FStar_Syntax_Syntax.n  in
                (match uu____11763 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11784 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11784
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1680_11814 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1680_11814.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1680_11814.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11818 =
                            let uu____11819 =
                              let uu____11826 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11826)  in
                            FStar_Syntax_Syntax.NT uu____11819  in
                          [uu____11818]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1686_11842 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1686_11842.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1686_11842.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11843 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11883 =
                  let uu____11890 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11890  in
                (match uu____11883 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11949 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11974 ->
               let uu____11975 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11975 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12288 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12288
       then
         let uu____12293 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12293
       else ());
      (let uu____12299 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12299
       then
         let uu____12304 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12304
       else ());
      (let uu____12309 = next_prob probs  in
       match uu____12309 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1713_12336 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1713_12336.wl_deferred);
               wl_deferred_to_tac = (uu___1713_12336.wl_deferred_to_tac);
               ctr = (uu___1713_12336.ctr);
               defer_ok = (uu___1713_12336.defer_ok);
               smt_ok = (uu___1713_12336.smt_ok);
               umax_heuristic_ok = (uu___1713_12336.umax_heuristic_ok);
               tcenv = (uu___1713_12336.tcenv);
               wl_implicits = (uu___1713_12336.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12345 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12345
                 then
                   let uu____12348 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____12348
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
                       (let uu____12355 =
                          defer_maybe_tac_lit
                            "deferring flex_rigid or flex_flex subtyping" tp
                            probs1
                           in
                        solve env uu____12355)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1725_12361 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1725_12361.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1725_12361.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1725_12361.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1725_12361.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1725_12361.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1725_12361.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1725_12361.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1725_12361.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1725_12361.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12381 =
                  let uu____12388 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12388, (probs.wl_implicits))  in
                Success uu____12381
            | uu____12394 ->
                let uu____12404 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12469  ->
                          match uu____12469 with
                          | (c,uu____12479,uu____12480) -> c < probs.ctr))
                   in
                (match uu____12404 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12528 =
                            let uu____12535 = as_deferred probs.wl_deferred
                               in
                            let uu____12536 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12535, uu____12536, (probs.wl_implicits))
                             in
                          Success uu____12528
                      | uu____12537 ->
                          let uu____12547 =
                            let uu___1739_12548 = probs  in
                            let uu____12549 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12570  ->
                                      match uu____12570 with
                                      | (uu____12578,uu____12579,y) -> y))
                               in
                            {
                              attempting = uu____12549;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1739_12548.wl_deferred_to_tac);
                              ctr = (uu___1739_12548.ctr);
                              defer_ok = (uu___1739_12548.defer_ok);
                              smt_ok = (uu___1739_12548.smt_ok);
                              umax_heuristic_ok =
                                (uu___1739_12548.umax_heuristic_ok);
                              tcenv = (uu___1739_12548.tcenv);
                              wl_implicits = (uu___1739_12548.wl_implicits)
                            }  in
                          solve env uu____12547))))

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
            let uu____12588 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12588 with
            | USolved wl1 ->
                let uu____12590 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12590
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12593 = defer_lit "" orig wl1  in
                solve env uu____12593

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
                  let uu____12644 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12644 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12647 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12660;
                  FStar_Syntax_Syntax.vars = uu____12661;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12664;
                  FStar_Syntax_Syntax.vars = uu____12665;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12678,uu____12679) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12687,FStar_Syntax_Syntax.Tm_uinst uu____12688) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12696 -> USolved wl

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
            ((let uu____12707 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12707
              then
                let uu____12712 = prob_to_string env orig  in
                let uu____12714 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12712 uu____12714
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
          let wl1 =
            let uu___1820_12728 = wl  in
            let uu____12729 =
              let uu____12739 =
                let uu____12747 = FStar_Thunk.mkv reason  in
                ((wl.ctr), uu____12747, orig)  in
              uu____12739 :: (wl.wl_deferred_to_tac)  in
            {
              attempting = (uu___1820_12728.attempting);
              wl_deferred = (uu___1820_12728.wl_deferred);
              wl_deferred_to_tac = uu____12729;
              ctr = (uu___1820_12728.ctr);
              defer_ok = (uu___1820_12728.defer_ok);
              smt_ok = (uu___1820_12728.smt_ok);
              umax_heuristic_ok = (uu___1820_12728.umax_heuristic_ok);
              tcenv = (uu___1820_12728.tcenv);
              wl_implicits = (uu___1820_12728.wl_implicits)
            }  in
          solve env wl1

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
               let uu____12842 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12842 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12897 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12897
                then
                  let uu____12902 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12904 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12902 uu____12904
                else ());
               (let uu____12909 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12909 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12955 = eq_prob t1 t2 wl2  in
                         (match uu____12955 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12976 ->
                         let uu____12985 = eq_prob t1 t2 wl2  in
                         (match uu____12985 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13035 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13050 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13051 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13050, uu____13051)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13056 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13057 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13056, uu____13057)
                            in
                         (match uu____13035 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13088 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13088 with
                                | (t1_hd,t1_args) ->
                                    let uu____13133 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13133 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13199 =
                                              let uu____13206 =
                                                let uu____13217 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13217 :: t1_args  in
                                              let uu____13234 =
                                                let uu____13243 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13243 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13292  ->
                                                   fun uu____13293  ->
                                                     fun uu____13294  ->
                                                       match (uu____13292,
                                                               uu____13293,
                                                               uu____13294)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13344),
                                                          (a2,uu____13346))
                                                           ->
                                                           let uu____13383 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13383
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13206
                                                uu____13234
                                               in
                                            match uu____13199 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1900_13409 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1900_13409.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1900_13409.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1900_13409.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1900_13409.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13420 =
                                                  solve env1 wl'  in
                                                (match uu____13420 with
                                                 | Success
                                                     (uu____13423,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13427 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13427))
                                                 | Failed uu____13428 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13460 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13460 with
                                | (t1_base,p1_opt) ->
                                    let uu____13496 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13496 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13595 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13595
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
                                               let uu____13648 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13648
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
                                               let uu____13680 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13680
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
                                               let uu____13712 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13712
                                           | uu____13715 -> t_base  in
                                         let uu____13732 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13732 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13746 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13746, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13753 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13753 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13789 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13789 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13825 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13825
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
                              let uu____13849 = combine t11 t21 wl2  in
                              (match uu____13849 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13882 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13882
                                     then
                                       let uu____13887 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13887
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13929 ts1 =
               match uu____13929 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13992 = pairwise out t wl2  in
                        (match uu____13992 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14028 =
               let uu____14039 = FStar_List.hd ts  in (uu____14039, [], wl1)
                in
             let uu____14048 = FStar_List.tl ts  in
             aux uu____14028 uu____14048  in
           let uu____14055 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14055 with
           | (this_flex,this_rigid) ->
               let uu____14081 =
                 let uu____14082 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14082.FStar_Syntax_Syntax.n  in
               (match uu____14081 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14107 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14107
                    then
                      let uu____14110 = destruct_flex_t this_flex wl  in
                      (match uu____14110 with
                       | (flex,wl1) ->
                           let uu____14117 = quasi_pattern env flex  in
                           (match uu____14117 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____14136 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14136
                                  then
                                    let uu____14141 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14141
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14148 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2010_14151 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2010_14151.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2010_14151.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2010_14151.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2010_14151.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2010_14151.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2010_14151.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2010_14151.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2010_14151.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2010_14151.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14148)
                | uu____14152 ->
                    ((let uu____14154 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14154
                      then
                        let uu____14159 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14159
                      else ());
                     (let uu____14164 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14164 with
                      | (u,_args) ->
                          let uu____14207 =
                            let uu____14208 = FStar_Syntax_Subst.compress u
                               in
                            uu____14208.FStar_Syntax_Syntax.n  in
                          (match uu____14207 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____14236 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14236 with
                                 | (u',uu____14255) ->
                                     let uu____14280 =
                                       let uu____14281 = whnf env u'  in
                                       uu____14281.FStar_Syntax_Syntax.n  in
                                     (match uu____14280 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14303 -> false)
                                  in
                               let uu____14305 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_14328  ->
                                         match uu___26_14328 with
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
                                              | uu____14342 -> false)
                                         | uu____14346 -> false))
                                  in
                               (match uu____14305 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14361 = whnf env this_rigid
                                         in
                                      let uu____14362 =
                                        FStar_List.collect
                                          (fun uu___27_14368  ->
                                             match uu___27_14368 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14374 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14374]
                                             | uu____14378 -> [])
                                          bounds_probs
                                         in
                                      uu____14361 :: uu____14362  in
                                    let uu____14379 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14379 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14412 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14427 =
                                               let uu____14428 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14428.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14427 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14440 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14440)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14451 -> bound  in
                                           let uu____14452 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14452)  in
                                         (match uu____14412 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14487 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14487
                                                then
                                                  let wl'1 =
                                                    let uu___2070_14493 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2070_14493.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2070_14493.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2070_14493.ctr);
                                                      defer_ok =
                                                        (uu___2070_14493.defer_ok);
                                                      smt_ok =
                                                        (uu___2070_14493.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2070_14493.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2070_14493.tcenv);
                                                      wl_implicits =
                                                        (uu___2070_14493.wl_implicits)
                                                    }  in
                                                  let uu____14494 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14494
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14500 =
                                                  solve_t env eq_prob
                                                    (let uu___2075_14502 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2075_14502.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2075_14502.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2075_14502.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2075_14502.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2075_14502.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2075_14502.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____14500 with
                                                | Success
                                                    (uu____14504,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2082_14508 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2082_14508.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2082_14508.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2082_14508.ctr);
                                                        defer_ok =
                                                          (uu___2082_14508.defer_ok);
                                                        smt_ok =
                                                          (uu___2082_14508.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2082_14508.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2082_14508.tcenv);
                                                        wl_implicits =
                                                          (uu___2082_14508.wl_implicits)
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
                                                    let uu____14525 =
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
                                                    ((let uu____14537 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14537
                                                      then
                                                        let uu____14542 =
                                                          let uu____14544 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14544
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14542
                                                      else ());
                                                     (let uu____14557 =
                                                        let uu____14572 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14572)
                                                         in
                                                      match uu____14557 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14594))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14620 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14620
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
                                                                  let uu____14640
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14640))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14665 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14665
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
                                                                    let uu____14685
                                                                    =
                                                                    let uu____14690
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14690
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14685
                                                                    [] wl2
                                                                     in
                                                                  let uu____14696
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14696))))
                                                      | uu____14697 ->
                                                          let uu____14712 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14712 p)))))))
                           | uu____14719 when flip ->
                               let uu____14720 =
                                 let uu____14722 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14724 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14722 uu____14724
                                  in
                               failwith uu____14720
                           | uu____14727 ->
                               let uu____14728 =
                                 let uu____14730 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14732 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14730 uu____14732
                                  in
                               failwith uu____14728)))))

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
                      (fun uu____14768  ->
                         match uu____14768 with
                         | (x,i) ->
                             let uu____14787 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14787, i)) bs_lhs
                     in
                  let uu____14790 = lhs  in
                  match uu____14790 with
                  | Flex (uu____14791,u_lhs,uu____14793) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14890 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14900 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14900, univ)
                             in
                          match uu____14890 with
                          | (k,univ) ->
                              let uu____14907 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14907 with
                               | (uu____14924,u,wl3) ->
                                   let uu____14927 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14927, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14953 =
                              let uu____14966 =
                                let uu____14977 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14977 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15028  ->
                                   fun uu____15029  ->
                                     match (uu____15028, uu____15029) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15130 =
                                           let uu____15137 =
                                             let uu____15140 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15140
                                              in
                                           copy_uvar u_lhs [] uu____15137 wl2
                                            in
                                         (match uu____15130 with
                                          | (uu____15169,t_a,wl3) ->
                                              let uu____15172 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15172 with
                                               | (uu____15191,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14966
                                ([], wl1)
                               in
                            (match uu____14953 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2195_15247 = ct  in
                                   let uu____15248 =
                                     let uu____15251 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15251
                                      in
                                   let uu____15266 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2195_15247.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2195_15247.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15248;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15266;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2195_15247.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2198_15284 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2198_15284.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2198_15284.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15287 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____15287 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15325 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15325 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15336 =
                                          let uu____15341 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15341)  in
                                        TERM uu____15336  in
                                      let uu____15342 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15342 with
                                       | (sub_prob,wl3) ->
                                           let uu____15356 =
                                             let uu____15357 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15357
                                              in
                                           solve env uu____15356))
                             | (x,imp)::formals2 ->
                                 let uu____15379 =
                                   let uu____15386 =
                                     let uu____15389 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15389
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15386 wl1
                                    in
                                 (match uu____15379 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15410 =
                                          let uu____15413 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15413
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15410 u_x
                                         in
                                      let uu____15414 =
                                        let uu____15417 =
                                          let uu____15420 =
                                            let uu____15421 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15421, imp)  in
                                          [uu____15420]  in
                                        FStar_List.append bs_terms
                                          uu____15417
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15414 formals2 wl2)
                              in
                           let uu____15448 = occurs_check u_lhs arrow1  in
                           (match uu____15448 with
                            | (uu____15461,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15477 =
                                    FStar_Thunk.mk
                                      (fun uu____15481  ->
                                         let uu____15482 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15482)
                                     in
                                  giveup_or_defer env orig wl uu____15477
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
              (let uu____15515 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15515
               then
                 let uu____15520 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15523 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15520 (rel_to_string (p_rel orig)) uu____15523
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15654 = rhs wl1 scope env1 subst1  in
                     (match uu____15654 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15677 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15677
                            then
                              let uu____15682 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15682
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15760 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15760 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2268_15762 = hd1  in
                       let uu____15763 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2268_15762.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2268_15762.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15763
                       }  in
                     let hd21 =
                       let uu___2271_15767 = hd2  in
                       let uu____15768 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2271_15767.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2271_15767.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15768
                       }  in
                     let uu____15771 =
                       let uu____15776 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15776
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15771 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15799 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15799
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15806 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15806 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15878 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15878
                                  in
                               ((let uu____15896 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15896
                                 then
                                   let uu____15901 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15903 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15901
                                     uu____15903
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15938 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15974 = aux wl [] env [] bs1 bs2  in
               match uu____15974 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16033 = attempt sub_probs wl2  in
                   solve env1 uu____16033)

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
            let uu___2309_16053 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2309_16053.wl_deferred_to_tac);
              ctr = (uu___2309_16053.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2309_16053.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16065 = try_solve env wl'  in
          match uu____16065 with
          | Success (uu____16066,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16079 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16079 wl)

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
            let uu____16085 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16085
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16098 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16098 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16132 = lhs1  in
                 match uu____16132 with
                 | Flex (uu____16135,ctx_u,uu____16137) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16145 ->
                           let uu____16146 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16146 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16195 = quasi_pattern env1 lhs1  in
                 match uu____16195 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16229) ->
                     let uu____16234 = lhs1  in
                     (match uu____16234 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16249 = occurs_check ctx_u rhs1  in
                          (match uu____16249 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16300 =
                                   let uu____16308 =
                                     let uu____16310 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16310
                                      in
                                   FStar_Util.Inl uu____16308  in
                                 (uu____16300, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16338 =
                                    let uu____16340 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16340  in
                                  if uu____16338
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16367 =
                                       let uu____16375 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16375  in
                                     let uu____16381 =
                                       restrict_all_uvars ctx_u uvars1 wl1
                                        in
                                     (uu____16367, uu____16381)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16425 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16425 with
                 | (rhs_hd,args) ->
                     let uu____16468 = FStar_Util.prefix args  in
                     (match uu____16468 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              FStar_Pervasives_Native.None
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16540 = lhs1  in
                          (match uu____16540 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16544 =
                                 let uu____16555 =
                                   let uu____16562 =
                                     let uu____16565 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16565
                                      in
                                   copy_uvar u_lhs [] uu____16562 wl1  in
                                 match uu____16555 with
                                 | (uu____16592,t_last_arg,wl2) ->
                                     let uu____16595 =
                                       let uu____16602 =
                                         let uu____16603 =
                                           let uu____16612 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16612]  in
                                         FStar_List.append bs_lhs uu____16603
                                          in
                                       copy_uvar u_lhs uu____16602 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16595 with
                                      | (uu____16647,lhs',wl3) ->
                                          let uu____16650 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16650 with
                                           | (uu____16667,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16544 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16688 =
                                        let uu____16689 =
                                          let uu____16694 =
                                            let uu____16695 =
                                              let uu____16698 =
                                                let uu____16703 =
                                                  let uu____16704 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lhs'_last_arg
                                                     in
                                                  [uu____16704]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  lhs' uu____16703
                                                 in
                                              uu____16698
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16695
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16694)  in
                                        TERM uu____16689  in
                                      [uu____16688]  in
                                    let uu____16729 =
                                      let uu____16736 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16736 with
                                      | (p1,wl3) ->
                                          let uu____16756 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16756 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16729 with
                                     | (sub_probs,wl3) ->
                                         let uu____16788 =
                                           let uu____16789 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16789  in
                                         solve env1 uu____16788))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16823 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16823 with
                   | (uu____16841,args) ->
                       (match args with | [] -> false | uu____16877 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16896 =
                     let uu____16897 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16897.FStar_Syntax_Syntax.n  in
                   match uu____16896 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16901 -> true
                   | uu____16917 -> false  in
                 let uu____16919 = quasi_pattern env1 lhs1  in
                 match uu____16919 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       FStar_Thunk.mk
                         (fun uu____16937  ->
                            let uu____16938 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____16938)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____16947 = is_app rhs1  in
                     if uu____16947
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____16952 = is_arrow rhs1  in
                        if uu____16952
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             FStar_Thunk.mk
                               (fun uu____16964  ->
                                  let uu____16965 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____16965)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____16969 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16969
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____16975 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16975
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____16980 = lhs  in
                   (match uu____16980 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____16984 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____16984 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____17002 =
                                 let uu____17006 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17006
                                  in
                               FStar_All.pipe_right uu____17002
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17027 = occurs_check ctx_uv rhs1  in
                             (match uu____17027 with
                              | (uvars1,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17056 =
                                      let uu____17057 =
                                        let uu____17059 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17059
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17057
                                       in
                                    giveup_or_defer env orig wl uu____17056
                                  else
                                    (let uu____17067 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17067
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars1 wl
                                          in
                                       let uu____17074 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17074
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            FStar_Thunk.mk
                                              (fun uu____17087  ->
                                                 let uu____17088 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17090 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17092 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17088 uu____17090
                                                   uu____17092)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17104 ->
                             if wl.defer_ok
                             then
                               let uu____17108 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17108
                             else
                               (let uu____17113 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17113 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17139 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17139
                                | (FStar_Util.Inl msg,uu____17141) ->
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
                  let uu____17159 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17159
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17165 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17165
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17170 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17170
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
                    (let uu____17177 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17177)
                  else
                    (let uu____17182 =
                       let uu____17199 = quasi_pattern env lhs  in
                       let uu____17206 = quasi_pattern env rhs  in
                       (uu____17199, uu____17206)  in
                     match uu____17182 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17249 = lhs  in
                         (match uu____17249 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17250;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17252;_},u_lhs,uu____17254)
                              ->
                              let uu____17257 = rhs  in
                              (match uu____17257 with
                               | Flex (uu____17258,u_rhs,uu____17260) ->
                                   let uu____17261 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17261
                                   then
                                     let uu____17268 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17268
                                   else
                                     (let uu____17271 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17271 with
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
                                          let uu____17303 =
                                            let uu____17310 =
                                              let uu____17313 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17313
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
                                              uu____17310
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17303 with
                                           | (uu____17319,w,wl1) ->
                                               let w_app =
                                                 let uu____17325 =
                                                   let uu____17330 =
                                                     FStar_List.map
                                                       (fun uu____17341  ->
                                                          match uu____17341
                                                          with
                                                          | (z,uu____17349)
                                                              ->
                                                              let uu____17354
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  z
                                                                 in
                                                              FStar_Syntax_Syntax.as_arg
                                                                uu____17354)
                                                       zs
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     w uu____17330
                                                    in
                                                 uu____17325
                                                   FStar_Pervasives_Native.None
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17356 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17356
                                                 then
                                                   let uu____17361 =
                                                     let uu____17365 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17367 =
                                                       let uu____17371 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17373 =
                                                         let uu____17377 =
                                                           term_to_string w
                                                            in
                                                         let uu____17379 =
                                                           let uu____17383 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17392 =
                                                             let uu____17396
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17405
                                                               =
                                                               let uu____17409
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17409]
                                                                in
                                                             uu____17396 ::
                                                               uu____17405
                                                              in
                                                           uu____17383 ::
                                                             uu____17392
                                                            in
                                                         uu____17377 ::
                                                           uu____17379
                                                          in
                                                       uu____17371 ::
                                                         uu____17373
                                                        in
                                                     uu____17365 ::
                                                       uu____17367
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17361
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17426 =
                                                       let uu____17431 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17431)
                                                        in
                                                     TERM uu____17426  in
                                                   let uu____17432 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17432
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17440 =
                                                          let uu____17445 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17445)
                                                           in
                                                        TERM uu____17440  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17446 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17446))))))
                     | uu____17447 ->
                         let uu____17464 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17464)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17518 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17518
            then
              let uu____17523 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17525 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17527 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17529 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17523 uu____17525 uu____17527 uu____17529
            else ());
           (let uu____17540 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17540 with
            | (head1,args1) ->
                let uu____17583 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17583 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17653 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17653 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17658 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17658)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17679 =
                         FStar_Thunk.mk
                           (fun uu____17686  ->
                              let uu____17687 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17689 = args_to_string args1  in
                              let uu____17693 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17695 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17687 uu____17689 uu____17693
                                uu____17695)
                          in
                       giveup env1 uu____17679 orig
                     else
                       (let uu____17702 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17707 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17707 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17702
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2581_17711 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2581_17711.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2581_17711.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2581_17711.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2581_17711.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2581_17711.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2581_17711.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2581_17711.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2581_17711.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17721 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17721
                                    else solve env1 wl2))
                        else
                          (let uu____17726 = base_and_refinement env1 t1  in
                           match uu____17726 with
                           | (base1,refinement1) ->
                               let uu____17751 = base_and_refinement env1 t2
                                  in
                               (match uu____17751 with
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
                                           let uu____17916 =
                                             FStar_List.fold_right
                                               (fun uu____17956  ->
                                                  fun uu____17957  ->
                                                    match (uu____17956,
                                                            uu____17957)
                                                    with
                                                    | (((a1,uu____18009),
                                                        (a2,uu____18011)),
                                                       (probs,wl3)) ->
                                                        let uu____18060 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18060
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17916 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18103 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18103
                                                 then
                                                   let uu____18108 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18108
                                                 else ());
                                                (let uu____18114 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18114
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
                                                    (let uu____18141 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18141 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18157 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18157
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18165 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18165))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18190 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18190 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18206 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18206
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18214 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18214)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18242 =
                                           match uu____18242 with
                                           | (prob,reason) ->
                                               ((let uu____18259 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18259
                                                 then
                                                   let uu____18264 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18266 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____18268 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____18264 uu____18266
                                                     uu____18268
                                                 else ());
                                                (let uu____18274 =
                                                   let uu____18283 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18286 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18283, uu____18286)
                                                    in
                                                 match uu____18274 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18299 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18299 with
                                                      | (head1',uu____18317)
                                                          ->
                                                          let uu____18342 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18342
                                                           with
                                                           | (head2',uu____18360)
                                                               ->
                                                               let uu____18385
                                                                 =
                                                                 let uu____18390
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18391
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18390,
                                                                   uu____18391)
                                                                  in
                                                               (match uu____18385
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18393
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18393
                                                                    then
                                                                    let uu____18398
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18400
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18402
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18404
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18398
                                                                    uu____18400
                                                                    uu____18402
                                                                    uu____18404
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18409
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2669_18417
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2669_18417.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18419
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18419
                                                                    then
                                                                    let uu____18424
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18424
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18429 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18441 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18441 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18449 =
                                             let uu____18450 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18450.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18449 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18455 -> false  in
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
                                          | uu____18458 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18461 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2689_18497 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2689_18497.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2689_18497.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2689_18497.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2689_18497.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2689_18497.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2689_18497.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2689_18497.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2689_18497.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18573 = destruct_flex_t scrutinee wl1  in
             match uu____18573 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18584 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18584 with
                  | (xs,pat_term,uu____18600,uu____18601) ->
                      let uu____18606 =
                        FStar_List.fold_left
                          (fun uu____18629  ->
                             fun x  ->
                               match uu____18629 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18650 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18650 with
                                    | (uu____18669,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18606 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18690 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18690 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2730_18707 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2730_18707.wl_deferred_to_tac);
                                    ctr = (uu___2730_18707.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2730_18707.umax_heuristic_ok);
                                    tcenv = (uu___2730_18707.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18718 = solve env1 wl'  in
                                (match uu____18718 with
                                 | Success (uu____18721,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2739_18725 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2739_18725.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2739_18725.wl_deferred_to_tac);
                                         ctr = (uu___2739_18725.ctr);
                                         defer_ok =
                                           (uu___2739_18725.defer_ok);
                                         smt_ok = (uu___2739_18725.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2739_18725.umax_heuristic_ok);
                                         tcenv = (uu___2739_18725.tcenv);
                                         wl_implicits =
                                           (uu___2739_18725.wl_implicits)
                                       }  in
                                     let uu____18726 = solve env1 wl'1  in
                                     (match uu____18726 with
                                      | Success
                                          (uu____18729,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18733 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18733))
                                      | Failed uu____18739 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18745 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18768 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18768
                 then
                   let uu____18773 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18775 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18773 uu____18775
                 else ());
                (let uu____18780 =
                   let uu____18801 =
                     let uu____18810 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18810)  in
                   let uu____18817 =
                     let uu____18826 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18826)  in
                   (uu____18801, uu____18817)  in
                 match uu____18780 with
                 | ((uu____18856,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18859;
                                   FStar_Syntax_Syntax.vars = uu____18860;_}),
                    (s,t)) ->
                     let uu____18931 =
                       let uu____18933 = is_flex scrutinee  in
                       Prims.op_Negation uu____18933  in
                     if uu____18931
                     then
                       ((let uu____18944 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18944
                         then
                           let uu____18949 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18949
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18968 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18968
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18983 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18983
                           then
                             let uu____18988 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18990 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18988 uu____18990
                           else ());
                          (let pat_discriminates uu___28_19015 =
                             match uu___28_19015 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19031;
                                  FStar_Syntax_Syntax.p = uu____19032;_},FStar_Pervasives_Native.None
                                ,uu____19033) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19047;
                                  FStar_Syntax_Syntax.p = uu____19048;_},FStar_Pervasives_Native.None
                                ,uu____19049) -> true
                             | uu____19076 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19179 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19179 with
                                       | (uu____19181,uu____19182,t') ->
                                           let uu____19200 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19200 with
                                            | (FullMatch ,uu____19212) ->
                                                true
                                            | (HeadMatch
                                               uu____19226,uu____19227) ->
                                                true
                                            | uu____19242 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19279 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19279
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19290 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19290 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19378,uu____19379) ->
                                       branches1
                                   | uu____19524 -> branches  in
                                 let uu____19579 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19588 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19588 with
                                        | (p,uu____19592,uu____19593) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19622  -> FStar_Util.Inr _19622)
                                   uu____19579))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19652 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19652 with
                                | (p,uu____19661,e) ->
                                    ((let uu____19680 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19680
                                      then
                                        let uu____19685 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19687 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19685 uu____19687
                                      else ());
                                     (let uu____19692 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19707  -> FStar_Util.Inr _19707)
                                        uu____19692)))))
                 | ((s,t),(uu____19710,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19713;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19714;_}))
                     ->
                     let uu____19783 =
                       let uu____19785 = is_flex scrutinee  in
                       Prims.op_Negation uu____19785  in
                     if uu____19783
                     then
                       ((let uu____19796 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19796
                         then
                           let uu____19801 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19801
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19820 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19820
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19835 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19835
                           then
                             let uu____19840 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19842 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19840 uu____19842
                           else ());
                          (let pat_discriminates uu___28_19867 =
                             match uu___28_19867 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19883;
                                  FStar_Syntax_Syntax.p = uu____19884;_},FStar_Pervasives_Native.None
                                ,uu____19885) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19899;
                                  FStar_Syntax_Syntax.p = uu____19900;_},FStar_Pervasives_Native.None
                                ,uu____19901) -> true
                             | uu____19928 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20031 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20031 with
                                       | (uu____20033,uu____20034,t') ->
                                           let uu____20052 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20052 with
                                            | (FullMatch ,uu____20064) ->
                                                true
                                            | (HeadMatch
                                               uu____20078,uu____20079) ->
                                                true
                                            | uu____20094 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20131 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20131
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20142 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20142 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20230,uu____20231) ->
                                       branches1
                                   | uu____20376 -> branches  in
                                 let uu____20431 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20440 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20440 with
                                        | (p,uu____20444,uu____20445) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20474  -> FStar_Util.Inr _20474)
                                   uu____20431))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20504 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20504 with
                                | (p,uu____20513,e) ->
                                    ((let uu____20532 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20532
                                      then
                                        let uu____20537 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20539 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20537 uu____20539
                                      else ());
                                     (let uu____20544 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20559  -> FStar_Util.Inr _20559)
                                        uu____20544)))))
                 | uu____20560 ->
                     ((let uu____20582 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20582
                       then
                         let uu____20587 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20589 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20587 uu____20589
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20635 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20635
            then
              let uu____20640 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20642 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20644 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20646 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20640 uu____20642 uu____20644 uu____20646
            else ());
           (let uu____20651 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20651 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20682,uu____20683) ->
                     let rec may_relate head3 =
                       let uu____20711 =
                         let uu____20712 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20712.FStar_Syntax_Syntax.n  in
                       match uu____20711 with
                       | FStar_Syntax_Syntax.Tm_name uu____20716 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20718 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20743 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20743 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20745 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20748
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20749 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20752,uu____20753) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20795) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20801) ->
                           may_relate t
                       | uu____20806 -> false  in
                     let uu____20808 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20808 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20821 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20821
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20831 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20831
                          then
                            let uu____20834 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20834 with
                             | (guard,wl2) ->
                                 let uu____20841 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20841)
                          else
                            (let uu____20844 =
                               FStar_Thunk.mk
                                 (fun uu____20851  ->
                                    let uu____20852 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20854 =
                                      let uu____20856 =
                                        let uu____20860 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20860
                                          (fun x  ->
                                             let uu____20867 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20867)
                                         in
                                      FStar_Util.dflt "" uu____20856  in
                                    let uu____20872 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20874 =
                                      let uu____20876 =
                                        let uu____20880 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20880
                                          (fun x  ->
                                             let uu____20887 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20887)
                                         in
                                      FStar_Util.dflt "" uu____20876  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20852 uu____20854 uu____20872
                                      uu____20874)
                                in
                             giveup env1 uu____20844 orig))
                 | (HeadMatch (true ),uu____20893) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20908 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20908 with
                        | (guard,wl2) ->
                            let uu____20915 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20915)
                     else
                       (let uu____20918 =
                          FStar_Thunk.mk
                            (fun uu____20923  ->
                               let uu____20924 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20926 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20924 uu____20926)
                           in
                        giveup env1 uu____20918 orig)
                 | (uu____20929,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2921_20943 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2921_20943.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2921_20943.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2921_20943.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2921_20943.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2921_20943.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2921_20943.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2921_20943.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2921_20943.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20970 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20970
          then
            let uu____20973 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20973
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20979 =
                let uu____20982 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20982  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20979 t1);
             (let uu____21001 =
                let uu____21004 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21004  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21001 t2);
             (let uu____21023 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21023
              then
                let uu____21027 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21029 =
                  let uu____21031 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21033 =
                    let uu____21035 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21035  in
                  Prims.op_Hat uu____21031 uu____21033  in
                let uu____21038 =
                  let uu____21040 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21042 =
                    let uu____21044 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21044  in
                  Prims.op_Hat uu____21040 uu____21042  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21027 uu____21029 uu____21038
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21051,uu____21052) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21068,FStar_Syntax_Syntax.Tm_delayed uu____21069) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21085,uu____21086) ->
                  let uu____21113 =
                    let uu___2952_21114 = problem  in
                    let uu____21115 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2952_21114.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21115;
                      FStar_TypeChecker_Common.relation =
                        (uu___2952_21114.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2952_21114.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2952_21114.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2952_21114.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2952_21114.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2952_21114.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2952_21114.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2952_21114.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21113 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21116,uu____21117) ->
                  let uu____21124 =
                    let uu___2958_21125 = problem  in
                    let uu____21126 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2958_21125.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21126;
                      FStar_TypeChecker_Common.relation =
                        (uu___2958_21125.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2958_21125.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2958_21125.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2958_21125.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2958_21125.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2958_21125.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2958_21125.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2958_21125.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21124 wl
              | (uu____21127,FStar_Syntax_Syntax.Tm_ascribed uu____21128) ->
                  let uu____21155 =
                    let uu___2964_21156 = problem  in
                    let uu____21157 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2964_21156.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2964_21156.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2964_21156.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21157;
                      FStar_TypeChecker_Common.element =
                        (uu___2964_21156.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2964_21156.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2964_21156.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2964_21156.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2964_21156.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2964_21156.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21155 wl
              | (uu____21158,FStar_Syntax_Syntax.Tm_meta uu____21159) ->
                  let uu____21166 =
                    let uu___2970_21167 = problem  in
                    let uu____21168 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2970_21167.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2970_21167.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2970_21167.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21168;
                      FStar_TypeChecker_Common.element =
                        (uu___2970_21167.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2970_21167.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2970_21167.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2970_21167.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2970_21167.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2970_21167.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21166 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21170),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21172)) ->
                  let uu____21181 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21181
              | (FStar_Syntax_Syntax.Tm_bvar uu____21182,uu____21183) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21185,FStar_Syntax_Syntax.Tm_bvar uu____21186) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_21256 =
                    match uu___29_21256 with
                    | [] -> c
                    | bs ->
                        let uu____21284 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21284
                     in
                  let uu____21295 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21295 with
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
                                    let uu____21444 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21444
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
                  let mk_t t l uu___30_21533 =
                    match uu___30_21533 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21575 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21575 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21720 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21721 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21720
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21721 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21723,uu____21724) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21755 -> true
                    | uu____21775 -> false  in
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
                      (let uu____21835 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3072_21843 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3072_21843.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3072_21843.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3072_21843.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3072_21843.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3072_21843.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3072_21843.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3072_21843.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3072_21843.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3072_21843.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3072_21843.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3072_21843.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3072_21843.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3072_21843.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3072_21843.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3072_21843.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3072_21843.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3072_21843.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3072_21843.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3072_21843.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3072_21843.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3072_21843.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3072_21843.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3072_21843.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3072_21843.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3072_21843.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3072_21843.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3072_21843.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3072_21843.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3072_21843.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3072_21843.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3072_21843.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3072_21843.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3072_21843.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3072_21843.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3072_21843.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3072_21843.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3072_21843.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3072_21843.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3072_21843.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3072_21843.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3072_21843.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3072_21843.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3072_21843.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3072_21843.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21835 with
                       | (uu____21848,ty,uu____21850) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21859 =
                                 let uu____21860 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21860.FStar_Syntax_Syntax.n  in
                               match uu____21859 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21863 ->
                                   let uu____21870 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21870
                               | uu____21871 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21874 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21874
                             then
                               let uu____21879 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21881 =
                                 let uu____21883 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21883
                                  in
                               let uu____21884 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21879 uu____21881 uu____21884
                             else ());
                            r1))
                     in
                  let uu____21889 =
                    let uu____21906 = maybe_eta t1  in
                    let uu____21913 = maybe_eta t2  in
                    (uu____21906, uu____21913)  in
                  (match uu____21889 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3093_21955 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3093_21955.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3093_21955.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3093_21955.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3093_21955.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3093_21955.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3093_21955.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3093_21955.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3093_21955.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21976 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21976
                       then
                         let uu____21979 = destruct_flex_t not_abs wl  in
                         (match uu____21979 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3110_21996 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3110_21996.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3110_21996.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3110_21996.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3110_21996.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3110_21996.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3110_21996.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3110_21996.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3110_21996.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21999 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21999 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22022 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22022
                       then
                         let uu____22025 = destruct_flex_t not_abs wl  in
                         (match uu____22025 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3110_22042 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3110_22042.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3110_22042.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3110_22042.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3110_22042.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3110_22042.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3110_22042.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3110_22042.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3110_22042.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22045 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22045 orig))
                   | uu____22048 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22066,FStar_Syntax_Syntax.Tm_abs uu____22067) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22098 -> true
                    | uu____22118 -> false  in
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
                      (let uu____22178 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3072_22186 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3072_22186.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3072_22186.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3072_22186.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3072_22186.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3072_22186.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3072_22186.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3072_22186.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3072_22186.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3072_22186.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3072_22186.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3072_22186.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3072_22186.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3072_22186.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3072_22186.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3072_22186.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3072_22186.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3072_22186.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3072_22186.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3072_22186.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3072_22186.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3072_22186.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3072_22186.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3072_22186.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3072_22186.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3072_22186.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3072_22186.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3072_22186.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3072_22186.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3072_22186.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3072_22186.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3072_22186.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3072_22186.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3072_22186.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3072_22186.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3072_22186.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3072_22186.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3072_22186.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3072_22186.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3072_22186.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3072_22186.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3072_22186.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3072_22186.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3072_22186.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3072_22186.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____22178 with
                       | (uu____22191,ty,uu____22193) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22202 =
                                 let uu____22203 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22203.FStar_Syntax_Syntax.n  in
                               match uu____22202 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22206 ->
                                   let uu____22213 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22213
                               | uu____22214 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22217 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22217
                             then
                               let uu____22222 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22224 =
                                 let uu____22226 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22226
                                  in
                               let uu____22227 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22222 uu____22224 uu____22227
                             else ());
                            r1))
                     in
                  let uu____22232 =
                    let uu____22249 = maybe_eta t1  in
                    let uu____22256 = maybe_eta t2  in
                    (uu____22249, uu____22256)  in
                  (match uu____22232 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3093_22298 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3093_22298.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3093_22298.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3093_22298.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3093_22298.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3093_22298.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3093_22298.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3093_22298.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3093_22298.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22319 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22319
                       then
                         let uu____22322 = destruct_flex_t not_abs wl  in
                         (match uu____22322 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3110_22339 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3110_22339.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3110_22339.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3110_22339.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3110_22339.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3110_22339.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3110_22339.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3110_22339.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3110_22339.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22342 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22342 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22365 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22365
                       then
                         let uu____22368 = destruct_flex_t not_abs wl  in
                         (match uu____22368 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3110_22385 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3110_22385.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3110_22385.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3110_22385.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3110_22385.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3110_22385.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3110_22385.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3110_22385.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3110_22385.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22388 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22388 orig))
                   | uu____22391 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22421 =
                    let uu____22426 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22426 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3133_22454 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3133_22454.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3133_22454.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3135_22456 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3135_22456.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3135_22456.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22457,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3133_22472 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3133_22472.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3133_22472.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3135_22474 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3135_22474.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3135_22474.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22475 -> (x1, x2)  in
                  (match uu____22421 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22494 = as_refinement false env t11  in
                       (match uu____22494 with
                        | (x12,phi11) ->
                            let uu____22502 = as_refinement false env t21  in
                            (match uu____22502 with
                             | (x22,phi21) ->
                                 ((let uu____22511 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22511
                                   then
                                     ((let uu____22516 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22518 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22520 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22516
                                         uu____22518 uu____22520);
                                      (let uu____22523 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22525 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22527 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22523
                                         uu____22525 uu____22527))
                                   else ());
                                  (let uu____22532 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22532 with
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
                                         let uu____22603 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22603
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22615 =
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
                                         (let uu____22628 =
                                            let uu____22631 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22631
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22628
                                            (p_guard base_prob));
                                         (let uu____22650 =
                                            let uu____22653 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22653
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22650
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22672 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22672)
                                          in
                                       let has_uvars =
                                         (let uu____22677 =
                                            let uu____22679 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22679
                                             in
                                          Prims.op_Negation uu____22677) ||
                                           (let uu____22683 =
                                              let uu____22685 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22685
                                               in
                                            Prims.op_Negation uu____22683)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22689 =
                                           let uu____22694 =
                                             let uu____22703 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22703]  in
                                           mk_t_problem wl1 uu____22694 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22689 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22726 =
                                                solve env1
                                                  (let uu___3178_22728 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3178_22728.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3178_22728.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3178_22728.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3178_22728.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3178_22728.tcenv);
                                                     wl_implicits =
                                                       (uu___3178_22728.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22726 with
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
                                                   (uu____22743,defer_to_tac,uu____22745)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22750 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22750
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3194_22759 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3194_22759.attempting);
                                                         wl_deferred =
                                                           (uu___3194_22759.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3194_22759.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3194_22759.defer_ok);
                                                         smt_ok =
                                                           (uu___3194_22759.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3194_22759.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3194_22759.tcenv);
                                                         wl_implicits =
                                                           (uu___3194_22759.wl_implicits)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22762 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22762))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22765,FStar_Syntax_Syntax.Tm_uvar uu____22766) ->
                  let uu____22791 = destruct_flex_t t1 wl  in
                  (match uu____22791 with
                   | (f1,wl1) ->
                       let uu____22798 = destruct_flex_t t2 wl1  in
                       (match uu____22798 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22805;
                    FStar_Syntax_Syntax.pos = uu____22806;
                    FStar_Syntax_Syntax.vars = uu____22807;_},uu____22808),FStar_Syntax_Syntax.Tm_uvar
                 uu____22809) ->
                  let uu____22858 = destruct_flex_t t1 wl  in
                  (match uu____22858 with
                   | (f1,wl1) ->
                       let uu____22865 = destruct_flex_t t2 wl1  in
                       (match uu____22865 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22872,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22873;
                    FStar_Syntax_Syntax.pos = uu____22874;
                    FStar_Syntax_Syntax.vars = uu____22875;_},uu____22876))
                  ->
                  let uu____22925 = destruct_flex_t t1 wl  in
                  (match uu____22925 with
                   | (f1,wl1) ->
                       let uu____22932 = destruct_flex_t t2 wl1  in
                       (match uu____22932 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22939;
                    FStar_Syntax_Syntax.pos = uu____22940;
                    FStar_Syntax_Syntax.vars = uu____22941;_},uu____22942),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22943;
                    FStar_Syntax_Syntax.pos = uu____22944;
                    FStar_Syntax_Syntax.vars = uu____22945;_},uu____22946))
                  ->
                  let uu____23019 = destruct_flex_t t1 wl  in
                  (match uu____23019 with
                   | (f1,wl1) ->
                       let uu____23026 = destruct_flex_t t2 wl1  in
                       (match uu____23026 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23033,uu____23034) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23047 = destruct_flex_t t1 wl  in
                  (match uu____23047 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23054;
                    FStar_Syntax_Syntax.pos = uu____23055;
                    FStar_Syntax_Syntax.vars = uu____23056;_},uu____23057),uu____23058)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23095 = destruct_flex_t t1 wl  in
                  (match uu____23095 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23102,FStar_Syntax_Syntax.Tm_uvar uu____23103) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23116,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23117;
                    FStar_Syntax_Syntax.pos = uu____23118;
                    FStar_Syntax_Syntax.vars = uu____23119;_},uu____23120))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23157,FStar_Syntax_Syntax.Tm_arrow uu____23158) ->
                  solve_t' env
                    (let uu___3295_23186 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3295_23186.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3295_23186.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3295_23186.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3295_23186.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3295_23186.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3295_23186.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3295_23186.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3295_23186.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3295_23186.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23187;
                    FStar_Syntax_Syntax.pos = uu____23188;
                    FStar_Syntax_Syntax.vars = uu____23189;_},uu____23190),FStar_Syntax_Syntax.Tm_arrow
                 uu____23191) ->
                  solve_t' env
                    (let uu___3295_23243 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3295_23243.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3295_23243.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3295_23243.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3295_23243.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3295_23243.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3295_23243.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3295_23243.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3295_23243.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3295_23243.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23244,FStar_Syntax_Syntax.Tm_uvar uu____23245) ->
                  let uu____23258 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23258
              | (uu____23259,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23260;
                    FStar_Syntax_Syntax.pos = uu____23261;
                    FStar_Syntax_Syntax.vars = uu____23262;_},uu____23263))
                  ->
                  let uu____23300 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23300
              | (FStar_Syntax_Syntax.Tm_uvar uu____23301,uu____23302) ->
                  let uu____23315 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23315
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23316;
                    FStar_Syntax_Syntax.pos = uu____23317;
                    FStar_Syntax_Syntax.vars = uu____23318;_},uu____23319),uu____23320)
                  ->
                  let uu____23357 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23357
              | (FStar_Syntax_Syntax.Tm_refine uu____23358,uu____23359) ->
                  let t21 =
                    let uu____23367 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23367  in
                  solve_t env
                    (let uu___3330_23393 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3330_23393.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3330_23393.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3330_23393.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3330_23393.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3330_23393.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3330_23393.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3330_23393.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3330_23393.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3330_23393.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23394,FStar_Syntax_Syntax.Tm_refine uu____23395) ->
                  let t11 =
                    let uu____23403 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23403  in
                  solve_t env
                    (let uu___3337_23429 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3337_23429.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3337_23429.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3337_23429.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3337_23429.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3337_23429.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3337_23429.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3337_23429.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3337_23429.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3337_23429.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23511 =
                    let uu____23512 = guard_of_prob env wl problem t1 t2  in
                    match uu____23512 with
                    | (guard,wl1) ->
                        let uu____23519 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23519
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23738 = br1  in
                        (match uu____23738 with
                         | (p1,w1,uu____23767) ->
                             let uu____23784 = br2  in
                             (match uu____23784 with
                              | (p2,w2,uu____23807) ->
                                  let uu____23812 =
                                    let uu____23814 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23814  in
                                  if uu____23812
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23841 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23841 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23878 = br2  in
                                         (match uu____23878 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23911 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23911
                                                 in
                                              let uu____23916 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23947,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23968) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24027 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24027 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23916
                                                (fun uu____24099  ->
                                                   match uu____24099 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24136 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24136
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24157
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24157
                                                              then
                                                                let uu____24162
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24164
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24162
                                                                  uu____24164
                                                              else ());
                                                             (let uu____24170
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24170
                                                                (fun
                                                                   uu____24206
                                                                    ->
                                                                   match uu____24206
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
                    | uu____24335 -> FStar_Pervasives_Native.None  in
                  let uu____24376 = solve_branches wl brs1 brs2  in
                  (match uu____24376 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24402 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24402 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24429 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24429 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24463 =
                                FStar_List.map
                                  (fun uu____24475  ->
                                     match uu____24475 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24463  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24484 =
                              let uu____24485 =
                                let uu____24486 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24486
                                  (let uu___3436_24494 = wl3  in
                                   {
                                     attempting =
                                       (uu___3436_24494.attempting);
                                     wl_deferred =
                                       (uu___3436_24494.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3436_24494.wl_deferred_to_tac);
                                     ctr = (uu___3436_24494.ctr);
                                     defer_ok = (uu___3436_24494.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3436_24494.umax_heuristic_ok);
                                     tcenv = (uu___3436_24494.tcenv);
                                     wl_implicits =
                                       (uu___3436_24494.wl_implicits)
                                   })
                                 in
                              solve env uu____24485  in
                            (match uu____24484 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24500 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24509 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24509 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24512,uu____24513) ->
                  let head1 =
                    let uu____24537 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24537
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24583 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24583
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24629 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24629
                    then
                      let uu____24633 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24635 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24637 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24633 uu____24635 uu____24637
                    else ());
                   (let no_free_uvars t =
                      (let uu____24651 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24651) &&
                        (let uu____24655 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24655)
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
                      let uu____24674 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24674 = FStar_Syntax_Util.Equal  in
                    let uu____24675 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24675
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24679 = equal t1 t2  in
                         (if uu____24679
                          then
                            let uu____24682 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24682
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24687 =
                            let uu____24694 = equal t1 t2  in
                            if uu____24694
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24707 = mk_eq2 wl env orig t1 t2  in
                               match uu____24707 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24687 with
                          | (guard,wl1) ->
                              let uu____24728 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24728))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24731,uu____24732) ->
                  let head1 =
                    let uu____24740 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24740
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24786 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24786
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24832 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24832
                    then
                      let uu____24836 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24838 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24840 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24836 uu____24838 uu____24840
                    else ());
                   (let no_free_uvars t =
                      (let uu____24854 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24854) &&
                        (let uu____24858 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24858)
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
                      let uu____24877 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24877 = FStar_Syntax_Util.Equal  in
                    let uu____24878 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24878
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24882 = equal t1 t2  in
                         (if uu____24882
                          then
                            let uu____24885 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24885
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24890 =
                            let uu____24897 = equal t1 t2  in
                            if uu____24897
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24910 = mk_eq2 wl env orig t1 t2  in
                               match uu____24910 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24890 with
                          | (guard,wl1) ->
                              let uu____24931 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24931))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24934,uu____24935) ->
                  let head1 =
                    let uu____24937 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24937
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24983 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24983
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25029 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25029
                    then
                      let uu____25033 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25035 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25037 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25033 uu____25035 uu____25037
                    else ());
                   (let no_free_uvars t =
                      (let uu____25051 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25051) &&
                        (let uu____25055 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25055)
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
                      let uu____25074 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25074 = FStar_Syntax_Util.Equal  in
                    let uu____25075 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25075
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25079 = equal t1 t2  in
                         (if uu____25079
                          then
                            let uu____25082 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25082
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25087 =
                            let uu____25094 = equal t1 t2  in
                            if uu____25094
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25107 = mk_eq2 wl env orig t1 t2  in
                               match uu____25107 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25087 with
                          | (guard,wl1) ->
                              let uu____25128 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25128))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25131,uu____25132) ->
                  let head1 =
                    let uu____25134 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25134
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25180 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25180
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25226 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25226
                    then
                      let uu____25230 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25232 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25234 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25230 uu____25232 uu____25234
                    else ());
                   (let no_free_uvars t =
                      (let uu____25248 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25248) &&
                        (let uu____25252 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25252)
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
                      let uu____25271 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25271 = FStar_Syntax_Util.Equal  in
                    let uu____25272 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25272
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25276 = equal t1 t2  in
                         (if uu____25276
                          then
                            let uu____25279 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25279
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25284 =
                            let uu____25291 = equal t1 t2  in
                            if uu____25291
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25304 = mk_eq2 wl env orig t1 t2  in
                               match uu____25304 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25284 with
                          | (guard,wl1) ->
                              let uu____25325 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25325))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25328,uu____25329) ->
                  let head1 =
                    let uu____25331 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25331
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25371 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25371
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25411 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25411
                    then
                      let uu____25415 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25417 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25419 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25415 uu____25417 uu____25419
                    else ());
                   (let no_free_uvars t =
                      (let uu____25433 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25433) &&
                        (let uu____25437 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25437)
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
                      let uu____25456 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25456 = FStar_Syntax_Util.Equal  in
                    let uu____25457 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25457
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25461 = equal t1 t2  in
                         (if uu____25461
                          then
                            let uu____25464 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25464
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25469 =
                            let uu____25476 = equal t1 t2  in
                            if uu____25476
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25489 = mk_eq2 wl env orig t1 t2  in
                               match uu____25489 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25469 with
                          | (guard,wl1) ->
                              let uu____25510 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25510))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25513,uu____25514) ->
                  let head1 =
                    let uu____25532 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25532
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25572 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25572
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25612 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25612
                    then
                      let uu____25616 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25618 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25620 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25616 uu____25618 uu____25620
                    else ());
                   (let no_free_uvars t =
                      (let uu____25634 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25634) &&
                        (let uu____25638 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25638)
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
                      let uu____25657 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25657 = FStar_Syntax_Util.Equal  in
                    let uu____25658 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25658
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25662 = equal t1 t2  in
                         (if uu____25662
                          then
                            let uu____25665 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25665
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25670 =
                            let uu____25677 = equal t1 t2  in
                            if uu____25677
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25690 = mk_eq2 wl env orig t1 t2  in
                               match uu____25690 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25670 with
                          | (guard,wl1) ->
                              let uu____25711 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25711))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25714,FStar_Syntax_Syntax.Tm_match uu____25715) ->
                  let head1 =
                    let uu____25739 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25739
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25779 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25779
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25819 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25819
                    then
                      let uu____25823 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25825 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25827 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25823 uu____25825 uu____25827
                    else ());
                   (let no_free_uvars t =
                      (let uu____25841 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25841) &&
                        (let uu____25845 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25845)
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
                      let uu____25864 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25864 = FStar_Syntax_Util.Equal  in
                    let uu____25865 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25865
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25869 = equal t1 t2  in
                         (if uu____25869
                          then
                            let uu____25872 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25872
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25877 =
                            let uu____25884 = equal t1 t2  in
                            if uu____25884
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25897 = mk_eq2 wl env orig t1 t2  in
                               match uu____25897 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25877 with
                          | (guard,wl1) ->
                              let uu____25918 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25918))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25921,FStar_Syntax_Syntax.Tm_uinst uu____25922) ->
                  let head1 =
                    let uu____25930 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25930
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25970 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25970
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26010 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26010
                    then
                      let uu____26014 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26016 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26018 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26014 uu____26016 uu____26018
                    else ());
                   (let no_free_uvars t =
                      (let uu____26032 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26032) &&
                        (let uu____26036 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26036)
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
                      let uu____26055 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26055 = FStar_Syntax_Util.Equal  in
                    let uu____26056 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26056
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26060 = equal t1 t2  in
                         (if uu____26060
                          then
                            let uu____26063 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26063
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26068 =
                            let uu____26075 = equal t1 t2  in
                            if uu____26075
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26088 = mk_eq2 wl env orig t1 t2  in
                               match uu____26088 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26068 with
                          | (guard,wl1) ->
                              let uu____26109 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26109))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26112,FStar_Syntax_Syntax.Tm_name uu____26113) ->
                  let head1 =
                    let uu____26115 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26115
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26155 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26155
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26195 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26195
                    then
                      let uu____26199 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26201 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26203 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26199 uu____26201 uu____26203
                    else ());
                   (let no_free_uvars t =
                      (let uu____26217 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26217) &&
                        (let uu____26221 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26221)
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
                      let uu____26240 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26240 = FStar_Syntax_Util.Equal  in
                    let uu____26241 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26241
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26245 = equal t1 t2  in
                         (if uu____26245
                          then
                            let uu____26248 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26248
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26253 =
                            let uu____26260 = equal t1 t2  in
                            if uu____26260
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26273 = mk_eq2 wl env orig t1 t2  in
                               match uu____26273 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26253 with
                          | (guard,wl1) ->
                              let uu____26294 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26294))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26297,FStar_Syntax_Syntax.Tm_constant uu____26298) ->
                  let head1 =
                    let uu____26300 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26300
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26340 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26340
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26380 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26380
                    then
                      let uu____26384 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26386 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26388 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26384 uu____26386 uu____26388
                    else ());
                   (let no_free_uvars t =
                      (let uu____26402 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26402) &&
                        (let uu____26406 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26406)
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
                      let uu____26425 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26425 = FStar_Syntax_Util.Equal  in
                    let uu____26426 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26426
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26430 = equal t1 t2  in
                         (if uu____26430
                          then
                            let uu____26433 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26433
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26438 =
                            let uu____26445 = equal t1 t2  in
                            if uu____26445
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26458 = mk_eq2 wl env orig t1 t2  in
                               match uu____26458 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26438 with
                          | (guard,wl1) ->
                              let uu____26479 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26479))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26482,FStar_Syntax_Syntax.Tm_fvar uu____26483) ->
                  let head1 =
                    let uu____26485 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26485
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26531 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26531
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26577 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26577
                    then
                      let uu____26581 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26583 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26585 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26581 uu____26583 uu____26585
                    else ());
                   (let no_free_uvars t =
                      (let uu____26599 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26599) &&
                        (let uu____26603 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26603)
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
                      let uu____26622 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26622 = FStar_Syntax_Util.Equal  in
                    let uu____26623 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26623
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26627 = equal t1 t2  in
                         (if uu____26627
                          then
                            let uu____26630 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26630
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26635 =
                            let uu____26642 = equal t1 t2  in
                            if uu____26642
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26655 = mk_eq2 wl env orig t1 t2  in
                               match uu____26655 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26635 with
                          | (guard,wl1) ->
                              let uu____26676 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26676))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26679,FStar_Syntax_Syntax.Tm_app uu____26680) ->
                  let head1 =
                    let uu____26698 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26698
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26738 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26738
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26778 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26778
                    then
                      let uu____26782 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26784 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26786 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26782 uu____26784 uu____26786
                    else ());
                   (let no_free_uvars t =
                      (let uu____26800 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26800) &&
                        (let uu____26804 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26804)
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
                      let uu____26823 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26823 = FStar_Syntax_Util.Equal  in
                    let uu____26824 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26824
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26828 = equal t1 t2  in
                         (if uu____26828
                          then
                            let uu____26831 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26831
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26836 =
                            let uu____26843 = equal t1 t2  in
                            if uu____26843
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26856 = mk_eq2 wl env orig t1 t2  in
                               match uu____26856 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26836 with
                          | (guard,wl1) ->
                              let uu____26877 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26877))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26880,FStar_Syntax_Syntax.Tm_let uu____26881) ->
                  let uu____26908 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26908
                  then
                    let uu____26911 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26911
                  else
                    (let uu____26914 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26914 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26917,uu____26918) ->
                  let uu____26932 =
                    let uu____26938 =
                      let uu____26940 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26942 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26944 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26946 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26940 uu____26942 uu____26944 uu____26946
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26938)
                     in
                  FStar_Errors.raise_error uu____26932
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26950,FStar_Syntax_Syntax.Tm_let uu____26951) ->
                  let uu____26965 =
                    let uu____26971 =
                      let uu____26973 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26975 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26977 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26979 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26973 uu____26975 uu____26977 uu____26979
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26971)
                     in
                  FStar_Errors.raise_error uu____26965
                    t1.FStar_Syntax_Syntax.pos
              | uu____26983 ->
                  let uu____26988 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26988 orig))))

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
          (let uu____27054 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27054
           then
             let uu____27059 =
               let uu____27061 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27061  in
             let uu____27062 =
               let uu____27064 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27064  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27059 uu____27062
           else ());
          (let uu____27068 =
             let uu____27070 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27070  in
           if uu____27068
           then
             let uu____27073 =
               FStar_Thunk.mk
                 (fun uu____27078  ->
                    let uu____27079 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27081 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27079 uu____27081)
                in
             giveup env uu____27073 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27103 =
                  FStar_Thunk.mk
                    (fun uu____27108  ->
                       let uu____27109 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27111 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27109 uu____27111)
                   in
                giveup env uu____27103 orig)
             else
               (let uu____27116 =
                  FStar_List.fold_left2
                    (fun uu____27137  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27137 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27158 =
                                 let uu____27163 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27164 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27163
                                   FStar_TypeChecker_Common.EQ uu____27164
                                   "effect universes"
                                  in
                               (match uu____27158 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27116 with
                | (univ_sub_probs,wl1) ->
                    let uu____27184 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27184 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27192 =
                           FStar_List.fold_right2
                             (fun uu____27229  ->
                                fun uu____27230  ->
                                  fun uu____27231  ->
                                    match (uu____27229, uu____27230,
                                            uu____27231)
                                    with
                                    | ((a1,uu____27275),(a2,uu____27277),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27310 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27310 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27192 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27337 =
                                  let uu____27340 =
                                    let uu____27343 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27343
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27340
                                   in
                                FStar_List.append univ_sub_probs uu____27337
                                 in
                              let guard =
                                let guard =
                                  let uu____27365 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27365  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3589_27374 = wl3  in
                                {
                                  attempting = (uu___3589_27374.attempting);
                                  wl_deferred = (uu___3589_27374.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3589_27374.wl_deferred_to_tac);
                                  ctr = (uu___3589_27374.ctr);
                                  defer_ok = (uu___3589_27374.defer_ok);
                                  smt_ok = (uu___3589_27374.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3589_27374.umax_heuristic_ok);
                                  tcenv = (uu___3589_27374.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27376 = attempt sub_probs wl5  in
                              solve env uu____27376))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27394 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27394
           then
             let uu____27399 =
               let uu____27401 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27401
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27403 =
               let uu____27405 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27405
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27399 uu____27403
           else ());
          (let uu____27410 =
             let uu____27415 =
               let uu____27420 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27420
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27415
               (fun uu____27437  ->
                  match uu____27437 with
                  | (c,g) ->
                      let uu____27448 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27448, g))
              in
           match uu____27410 with
           | (c12,g_lift) ->
               ((let uu____27452 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27452
                 then
                   let uu____27457 =
                     let uu____27459 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27459
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27461 =
                     let uu____27463 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27463
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27457 uu____27461
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3609_27473 = wl  in
                     {
                       attempting = (uu___3609_27473.attempting);
                       wl_deferred = (uu___3609_27473.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3609_27473.wl_deferred_to_tac);
                       ctr = (uu___3609_27473.ctr);
                       defer_ok = (uu___3609_27473.defer_ok);
                       smt_ok = (uu___3609_27473.smt_ok);
                       umax_heuristic_ok =
                         (uu___3609_27473.umax_heuristic_ok);
                       tcenv = (uu___3609_27473.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____27474 =
                     let rec is_uvar1 t =
                       let uu____27488 =
                         let uu____27489 = FStar_Syntax_Subst.compress t  in
                         uu____27489.FStar_Syntax_Syntax.n  in
                       match uu____27488 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27493 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27508) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27514) ->
                           is_uvar1 t1
                       | uu____27539 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27573  ->
                          fun uu____27574  ->
                            fun uu____27575  ->
                              match (uu____27573, uu____27574, uu____27575)
                              with
                              | ((a1,uu____27619),(a2,uu____27621),(is_sub_probs,wl2))
                                  ->
                                  let uu____27654 = is_uvar1 a1  in
                                  if uu____27654
                                  then
                                    ((let uu____27664 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27664
                                      then
                                        let uu____27669 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27671 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27669 uu____27671
                                      else ());
                                     (let uu____27676 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27676 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27474 with
                   | (is_sub_probs,wl2) ->
                       let uu____27704 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27704 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27712 =
                              let uu____27717 =
                                let uu____27718 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27718
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27717
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27712 with
                             | (uu____27725,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27736 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27738 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27736 s uu____27738
                                    in
                                 let uu____27741 =
                                   let uu____27770 =
                                     let uu____27771 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27771.FStar_Syntax_Syntax.n  in
                                   match uu____27770 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27831 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27831 with
                                        | (a::bs1,c3) ->
                                            let uu____27887 =
                                              let uu____27906 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27906
                                                (fun uu____28010  ->
                                                   match uu____28010 with
                                                   | (l1,l2) ->
                                                       let uu____28083 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28083))
                                               in
                                            (match uu____27887 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28188 ->
                                       let uu____28189 =
                                         let uu____28195 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28195)
                                          in
                                       FStar_Errors.raise_error uu____28189 r
                                    in
                                 (match uu____27741 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28271 =
                                        let uu____28278 =
                                          let uu____28279 =
                                            let uu____28280 =
                                              let uu____28287 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28287,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28280
                                             in
                                          [uu____28279]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28278
                                          (fun b  ->
                                             let uu____28303 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28305 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28307 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28303 uu____28305
                                               uu____28307) r
                                         in
                                      (match uu____28271 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28317 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28317
                                             then
                                               let uu____28322 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28331 =
                                                          let uu____28333 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28333
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28331) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28322
                                             else ());
                                            (let wl4 =
                                               let uu___3681_28341 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3681_28341.attempting);
                                                 wl_deferred =
                                                   (uu___3681_28341.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3681_28341.wl_deferred_to_tac);
                                                 ctr = (uu___3681_28341.ctr);
                                                 defer_ok =
                                                   (uu___3681_28341.defer_ok);
                                                 smt_ok =
                                                   (uu___3681_28341.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3681_28341.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3681_28341.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28366 =
                                                        let uu____28373 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28373, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28366) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28390 =
                                               let f_sort_is =
                                                 let uu____28400 =
                                                   let uu____28401 =
                                                     let uu____28404 =
                                                       let uu____28405 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28405.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28404
                                                      in
                                                   uu____28401.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28400 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28416,uu____28417::is)
                                                     ->
                                                     let uu____28459 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28459
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28492 ->
                                                     let uu____28493 =
                                                       let uu____28499 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28499)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28493 r
                                                  in
                                               let uu____28505 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28540  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28540
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28561 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28561
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28505
                                                in
                                             match uu____28390 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28586 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28586
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28587 =
                                                   let g_sort_is =
                                                     let uu____28597 =
                                                       let uu____28598 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28598.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28597 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28603,uu____28604::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28664 ->
                                                         let uu____28665 =
                                                           let uu____28671 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28671)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28665 r
                                                      in
                                                   let uu____28677 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28712  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28712
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28733
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28733
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28677
                                                    in
                                                 (match uu____28587 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28760 =
                                                          let uu____28765 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28766 =
                                                            let uu____28767 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28767
                                                             in
                                                          (uu____28765,
                                                            uu____28766)
                                                           in
                                                        match uu____28760
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28795 =
                                                          let uu____28798 =
                                                            let uu____28801 =
                                                              let uu____28804
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28804
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28801
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28798
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28795
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28828 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28828
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
                                                        let uu____28839 =
                                                          let uu____28842 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28845  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28845)
                                                            uu____28842
                                                           in
                                                        solve_prob orig
                                                          uu____28839 [] wl6
                                                         in
                                                      let uu____28846 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28846))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28869 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28871 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28871]
              | x -> x  in
            let c12 =
              let uu___3747_28874 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3747_28874.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3747_28874.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3747_28874.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3747_28874.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28875 =
              let uu____28880 =
                FStar_All.pipe_right
                  (let uu___3750_28882 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3750_28882.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3750_28882.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3750_28882.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3750_28882.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28880
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28875
              (fun uu____28896  ->
                 match uu____28896 with
                 | (c,g) ->
                     let uu____28903 =
                       let uu____28905 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28905  in
                     if uu____28903
                     then
                       let uu____28908 =
                         let uu____28914 =
                           let uu____28916 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28918 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28916 uu____28918
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28914)
                          in
                       FStar_Errors.raise_error uu____28908 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28924 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28924
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28930 = lift_c1 ()  in
               solve_eq uu____28930 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28939  ->
                         match uu___31_28939 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28944 -> false))
                  in
               let uu____28946 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28976)::uu____28977,(wp2,uu____28979)::uu____28980)
                     -> (wp1, wp2)
                 | uu____29053 ->
                     let uu____29078 =
                       let uu____29084 =
                         let uu____29086 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____29088 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____29086 uu____29088
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____29084)
                        in
                     FStar_Errors.raise_error uu____29078
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28946 with
               | (wpc1,wpc2) ->
                   let uu____29098 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____29098
                   then
                     let uu____29101 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29101 wl
                   else
                     (let uu____29105 =
                        let uu____29112 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____29112  in
                      match uu____29105 with
                      | (c2_decl,qualifiers) ->
                          let uu____29133 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____29133
                          then
                            let c1_repr =
                              let uu____29140 =
                                let uu____29141 =
                                  let uu____29142 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____29142  in
                                let uu____29143 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29141 uu____29143
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29140
                               in
                            let c2_repr =
                              let uu____29146 =
                                let uu____29147 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____29148 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29147 uu____29148
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29146
                               in
                            let uu____29150 =
                              let uu____29155 =
                                let uu____29157 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____29159 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____29157
                                  uu____29159
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____29155
                               in
                            (match uu____29150 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____29165 = attempt [prob] wl2  in
                                 solve env uu____29165)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____29185 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____29185
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____29208 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____29208
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
                                        let uu____29218 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____29218 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____29225 =
                                        let uu____29232 =
                                          let uu____29233 =
                                            let uu____29250 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29253 =
                                              let uu____29264 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29264; wpc1_2]  in
                                            (uu____29250, uu____29253)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29233
                                           in
                                        FStar_Syntax_Syntax.mk uu____29232
                                         in
                                      uu____29225
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
                                     let uu____29313 =
                                       let uu____29320 =
                                         let uu____29321 =
                                           let uu____29338 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29341 =
                                             let uu____29352 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29361 =
                                               let uu____29372 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29372; wpc1_2]  in
                                             uu____29352 :: uu____29361  in
                                           (uu____29338, uu____29341)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29321
                                          in
                                       FStar_Syntax_Syntax.mk uu____29320  in
                                     uu____29313 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____29426 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____29426
                              then
                                let uu____29431 =
                                  let uu____29433 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____29433
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____29431
                              else ());
                             (let uu____29437 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____29437 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____29446 =
                                      let uu____29449 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _29452  ->
                                           FStar_Pervasives_Native.Some
                                             _29452) uu____29449
                                       in
                                    solve_prob orig uu____29446 [] wl1  in
                                  let uu____29453 = attempt [base_prob] wl2
                                     in
                                  solve env uu____29453))))
           in
        let uu____29454 = FStar_Util.physical_equality c1 c2  in
        if uu____29454
        then
          let uu____29457 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29457
        else
          ((let uu____29461 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29461
            then
              let uu____29466 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29468 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29466
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29468
            else ());
           (let uu____29473 =
              let uu____29482 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29485 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29482, uu____29485)  in
            match uu____29473 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29503),FStar_Syntax_Syntax.Total
                    (t2,uu____29505)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29522 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29522 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29524,FStar_Syntax_Syntax.Total uu____29525) ->
                     let uu____29542 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29542 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29546),FStar_Syntax_Syntax.Total
                    (t2,uu____29548)) ->
                     let uu____29565 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29565 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29568),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29570)) ->
                     let uu____29587 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29587 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29590),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29592)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29609 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29609 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29612),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29614)) ->
                     let uu____29631 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29631 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29634,FStar_Syntax_Syntax.Comp uu____29635) ->
                     let uu____29644 =
                       let uu___3874_29647 = problem  in
                       let uu____29650 =
                         let uu____29651 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29651
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3874_29647.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29650;
                         FStar_TypeChecker_Common.relation =
                           (uu___3874_29647.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3874_29647.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3874_29647.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3874_29647.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3874_29647.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3874_29647.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3874_29647.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3874_29647.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29644 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29652,FStar_Syntax_Syntax.Comp uu____29653) ->
                     let uu____29662 =
                       let uu___3874_29665 = problem  in
                       let uu____29668 =
                         let uu____29669 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29669
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3874_29665.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29668;
                         FStar_TypeChecker_Common.relation =
                           (uu___3874_29665.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3874_29665.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3874_29665.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3874_29665.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3874_29665.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3874_29665.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3874_29665.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3874_29665.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29662 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29670,FStar_Syntax_Syntax.GTotal uu____29671) ->
                     let uu____29680 =
                       let uu___3886_29683 = problem  in
                       let uu____29686 =
                         let uu____29687 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29687
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3886_29683.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3886_29683.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3886_29683.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29686;
                         FStar_TypeChecker_Common.element =
                           (uu___3886_29683.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3886_29683.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3886_29683.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3886_29683.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3886_29683.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3886_29683.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29680 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29688,FStar_Syntax_Syntax.Total uu____29689) ->
                     let uu____29698 =
                       let uu___3886_29701 = problem  in
                       let uu____29704 =
                         let uu____29705 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29705
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3886_29701.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3886_29701.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3886_29701.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29704;
                         FStar_TypeChecker_Common.element =
                           (uu___3886_29701.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3886_29701.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3886_29701.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3886_29701.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3886_29701.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3886_29701.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29698 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29706,FStar_Syntax_Syntax.Comp uu____29707) ->
                     let uu____29708 =
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
                     if uu____29708
                     then
                       let uu____29711 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29711 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29718 =
                            let uu____29723 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29723
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29732 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29733 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29732, uu____29733))
                             in
                          match uu____29718 with
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
                           (let uu____29741 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29741
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29749 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29749 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29752 =
                                  FStar_Thunk.mk
                                    (fun uu____29757  ->
                                       let uu____29758 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29760 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29758 uu____29760)
                                   in
                                giveup env uu____29752 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29771 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29771 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29821 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29821 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29846 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29877  ->
                match uu____29877 with
                | (u1,u2) ->
                    let uu____29885 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29887 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29885 uu____29887))
         in
      FStar_All.pipe_right uu____29846 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29924,[])) when
          let uu____29951 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29951 -> "{}"
      | uu____29954 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29981 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29981
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30012 =
              FStar_List.map
                (fun uu____30026  ->
                   match uu____30026 with
                   | (msg,x) ->
                       let uu____30037 =
                         let uu____30039 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30039  in
                       Prims.op_Hat msg uu____30037) defs
               in
            FStar_All.pipe_right uu____30012 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30049 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30051 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30053 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30049 uu____30051 uu____30053 imps
  
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
                  let uu____30110 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30110
                  then
                    let uu____30118 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30120 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30118
                      (rel_to_string rel) uu____30120
                  else "TOP"  in
                let uu____30126 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30126 with
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
              let uu____30186 =
                let uu____30189 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30192  -> FStar_Pervasives_Native.Some _30192)
                  uu____30189
                 in
              FStar_Syntax_Syntax.new_bv uu____30186 t1  in
            let uu____30193 =
              let uu____30198 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30198
               in
            match uu____30193 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____30270 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30270
         then
           let uu____30275 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30275
         else ());
        (let uu____30282 =
           FStar_Util.record_time (fun uu____30289  -> solve env probs)  in
         match uu____30282 with
         | (sol,ms) ->
             ((let uu____30303 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30303
               then
                 let uu____30308 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30308
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30324 =
                     FStar_Util.record_time
                       (fun uu____30331  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30324 with
                    | ((),ms1) ->
                        ((let uu____30344 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30344
                          then
                            let uu____30349 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30349
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30363 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30363
                     then
                       let uu____30370 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30370
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
          ((let uu____30398 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30398
            then
              let uu____30403 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30403
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30411 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30411
             then
               let uu____30416 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30416
             else ());
            (let f2 =
               let uu____30422 =
                 let uu____30423 = FStar_Syntax_Util.unmeta f1  in
                 uu____30423.FStar_Syntax_Syntax.n  in
               match uu____30422 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30427 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4005_30428 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4005_30428.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4005_30428.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4005_30428.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4005_30428.FStar_TypeChecker_Common.implicits)
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
            let uu____30480 =
              let uu____30481 =
                let uu____30482 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30483  ->
                       FStar_TypeChecker_Common.NonTrivial _30483)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30482;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30481  in
            FStar_All.pipe_left
              (fun _30490  -> FStar_Pervasives_Native.Some _30490)
              uu____30480
  
let with_guard_no_simp :
  'Auu____30500 .
    'Auu____30500 ->
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
            let uu____30549 =
              let uu____30550 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30551  -> FStar_TypeChecker_Common.NonTrivial _30551)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30550;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30549
  
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
          (let uu____30584 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30584
           then
             let uu____30589 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30591 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30589
               uu____30591
           else ());
          (let uu____30596 =
             let uu____30601 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30601
              in
           match uu____30596 with
           | (prob,wl) ->
               let g =
                 let uu____30609 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30619  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30609  in
               ((let uu____30641 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30641
                 then
                   let uu____30646 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30646
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
        let uu____30667 = try_teq true env t1 t2  in
        match uu____30667 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30672 = FStar_TypeChecker_Env.get_range env  in
              let uu____30673 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30672 uu____30673);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30681 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30681
              then
                let uu____30686 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30688 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30690 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30686
                  uu____30688 uu____30690
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
        (let uu____30714 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30714
         then
           let uu____30719 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30721 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30719
             uu____30721
         else ());
        (let uu____30726 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30726 with
         | (prob,x,wl) ->
             let g =
               let uu____30741 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30752  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30741  in
             ((let uu____30774 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30774
               then
                 let uu____30779 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30779
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30787 =
                     let uu____30788 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30788 g1  in
                   FStar_Pervasives_Native.Some uu____30787)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30810 = FStar_TypeChecker_Env.get_range env  in
          let uu____30811 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30810 uu____30811
  
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
        (let uu____30840 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30840
         then
           let uu____30845 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30847 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30845 uu____30847
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30858 =
           let uu____30865 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30865 "sub_comp"
            in
         match uu____30858 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30878 =
                 FStar_Util.record_time
                   (fun uu____30890  ->
                      let uu____30891 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30902  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30891)
                  in
               match uu____30878 with
               | (r,ms) ->
                   ((let uu____30934 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30934
                     then
                       let uu____30939 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30941 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30943 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30939 uu____30941
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30943
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
      fun uu____30981  ->
        match uu____30981 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31024 =
                 let uu____31030 =
                   let uu____31032 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31034 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31032 uu____31034
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31030)  in
               let uu____31038 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31024 uu____31038)
               in
            let equiv1 v1 v' =
              let uu____31051 =
                let uu____31056 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____31057 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31056, uu____31057)  in
              match uu____31051 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31077 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____31108 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____31108 with
                      | FStar_Syntax_Syntax.U_unif uu____31115 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31144  ->
                                    match uu____31144 with
                                    | (u,v') ->
                                        let uu____31153 = equiv1 v1 v'  in
                                        if uu____31153
                                        then
                                          let uu____31158 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____31158 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____31179 -> []))
               in
            let uu____31184 =
              let wl =
                let uu___4118_31188 = empty_worklist env  in
                {
                  attempting = (uu___4118_31188.attempting);
                  wl_deferred = (uu___4118_31188.wl_deferred);
                  wl_deferred_to_tac = (uu___4118_31188.wl_deferred_to_tac);
                  ctr = (uu___4118_31188.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4118_31188.smt_ok);
                  umax_heuristic_ok = (uu___4118_31188.umax_heuristic_ok);
                  tcenv = (uu___4118_31188.tcenv);
                  wl_implicits = (uu___4118_31188.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31207  ->
                      match uu____31207 with
                      | (lb,v1) ->
                          let uu____31214 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31214 with
                           | USolved wl1 -> ()
                           | uu____31217 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31228 =
              match uu____31228 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31240) -> true
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
                      uu____31264,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31266,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31277) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31285,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31294 -> false)
               in
            let uu____31300 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31317  ->
                      match uu____31317 with
                      | (u,v1) ->
                          let uu____31325 = check_ineq (u, v1)  in
                          if uu____31325
                          then true
                          else
                            ((let uu____31333 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31333
                              then
                                let uu____31338 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31340 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31338
                                  uu____31340
                              else ());
                             false)))
               in
            if uu____31300
            then ()
            else
              ((let uu____31350 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31350
                then
                  ((let uu____31356 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31356);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31368 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31368))
                else ());
               (let uu____31381 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31381))
  
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
        let fail1 uu____31456 =
          match uu____31456 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4195_31483 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4195_31483.attempting);
            wl_deferred = (uu___4195_31483.wl_deferred);
            wl_deferred_to_tac = (uu___4195_31483.wl_deferred_to_tac);
            ctr = (uu___4195_31483.ctr);
            defer_ok;
            smt_ok = (uu___4195_31483.smt_ok);
            umax_heuristic_ok = (uu___4195_31483.umax_heuristic_ok);
            tcenv = (uu___4195_31483.tcenv);
            wl_implicits = (uu___4195_31483.wl_implicits)
          }  in
        (let uu____31486 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31486
         then
           let uu____31491 = FStar_Util.string_of_bool defer_ok  in
           let uu____31493 = wl_to_string wl  in
           let uu____31495 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31491 uu____31493 uu____31495
         else ());
        (let g1 =
           let uu____31501 = solve_and_commit env wl fail1  in
           match uu____31501 with
           | FStar_Pervasives_Native.Some
               (uu____31510::uu____31511,uu____31512,uu____31513) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
               let uu___4212_31547 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4212_31547.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred_to_tac =
                   (FStar_List.append
                      g.FStar_TypeChecker_Common.deferred_to_tac defer_to_tac);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4212_31547.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____31553 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4217_31564 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4217_31564.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4217_31564.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4217_31564.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4217_31564.FStar_TypeChecker_Common.implicits)
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
          (let uu____31640 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31640
           then
             let uu____31645 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31645
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4231_31652 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4231_31652.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4231_31652.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4231_31652.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4231_31652.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31653 =
             let uu____31655 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31655  in
           if uu____31653
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____31667 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31668 =
                        let uu____31670 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31670
                         in
                      FStar_Errors.diag uu____31667 uu____31668)
                   else ();
                   (let vc1 =
                      let uu____31676 =
                        let uu____31680 =
                          let uu____31682 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31682  in
                        FStar_Pervasives_Native.Some uu____31680  in
                      FStar_Profiling.profile
                        (fun uu____31685  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31676 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____31689 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31690 =
                         let uu____31692 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31692
                          in
                       FStar_Errors.diag uu____31689 uu____31690)
                    else ();
                    (let uu____31698 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31698 "discharge_guard'" env vc1);
                    (let uu____31700 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31700 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____31709 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31710 =
                                 let uu____31712 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31712
                                  in
                               FStar_Errors.diag uu____31709 uu____31710)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31722 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31723 =
                                 let uu____31725 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31725
                                  in
                               FStar_Errors.diag uu____31722 uu____31723)
                            else ();
                            (let vcs =
                               let uu____31739 = FStar_Options.use_tactics ()
                                  in
                               if uu____31739
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31761  ->
                                      (let uu____31763 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31763);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31807  ->
                                               match uu____31807 with
                                               | (env1,goal,opts) ->
                                                   let uu____31823 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31823, opts)))))
                               else
                                 (let uu____31827 =
                                    let uu____31834 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31834)  in
                                  [uu____31827])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31867  ->
                                     match uu____31867 with
                                     | (env1,goal,opts) ->
                                         let uu____31877 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31877 with
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
                                                 (let uu____31888 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31889 =
                                                    let uu____31891 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31893 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31891 uu____31893
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31888 uu____31889)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31900 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31901 =
                                                    let uu____31903 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31903
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31900 uu____31901)
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
      let uu____31921 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31921 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31930 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31930
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31944 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31944 with
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
        let uu____31974 = try_teq false env t1 t2  in
        match uu____31974 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (teq_maybe_defer :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let should_defer =
          let uu____32004 =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          match uu____32004 with | [] -> false | uu____32009 -> true  in
        if should_defer
        then
          let uu____32014 =
            let uu____32019 = FStar_TypeChecker_Env.get_range env  in
            new_t_problem (empty_worklist env) env t1
              FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
              uu____32019
             in
          match uu____32014 with
          | (prob,wl) ->
              let wl1 =
                let uu____32023 =
                  FStar_Thunk.mkv
                    "deferring for user-provided resolve_implicits hook"
                   in
                defer uu____32023 prob wl  in
              let g =
                let uu____32029 =
                  solve_and_commit env wl1
                    (fun uu____32039  -> FStar_Pervasives_Native.None)
                   in
                FStar_All.pipe_left (with_guard env prob) uu____32029  in
              let g1 = FStar_Option.get g  in
              ((let uu____32062 =
                  FStar_TypeChecker_Env.debug env
                    (FStar_Options.Other "ResolveImplicitsHook")
                   in
                if uu____32062
                then
                  let uu____32066 =
                    let uu____32068 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Range.string_of_range uu____32068  in
                  let uu____32069 = guard_to_string env g1  in
                  FStar_Util.print2 "(%s): Deferred unification: %s\n"
                    uu____32066 uu____32069
                else ());
               g1)
        else teq env t1 t2
  
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
            let uu____32108 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32108 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32115 ->
                     let uu____32116 =
                       let uu____32117 = FStar_Syntax_Subst.compress r  in
                       uu____32117.FStar_Syntax_Syntax.n  in
                     (match uu____32116 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32122) ->
                          unresolved ctx_u'
                      | uu____32139 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32163 = acc  in
            match uu____32163 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____32182 = hd1  in
                     (match uu____32182 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____32193 = unresolved ctx_u  in
                             if uu____32193
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32204 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32204
                                     then
                                       let uu____32208 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32208
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32217 = teq_nosmt env1 t tm
                                          in
                                       match uu____32217 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4360_32227 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4360_32227.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4360_32227.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4360_32227.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4360_32227.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4360_32227.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4360_32227.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4360_32227.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4363_32229 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4363_32229.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4363_32229.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4363_32229.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                               | uu____32232 ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4368_32244 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4368_32244.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4368_32244.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4368_32244.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4368_32244.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4368_32244.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4368_32244.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4368_32244.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4368_32244.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4368_32244.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4368_32244.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4368_32244.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4368_32244.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4368_32244.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4368_32244.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4368_32244.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4368_32244.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4368_32244.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4368_32244.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4368_32244.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4368_32244.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4368_32244.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4368_32244.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4368_32244.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4368_32244.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4368_32244.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4368_32244.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4368_32244.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4368_32244.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4368_32244.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4368_32244.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4368_32244.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4368_32244.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4368_32244.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4368_32244.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4368_32244.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4368_32244.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4368_32244.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4368_32244.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4368_32244.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4368_32244.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4368_32244.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4368_32244.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4368_32244.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4368_32244.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4368_32244.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4368_32244.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4373_32249 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4373_32249.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4373_32249.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4373_32249.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4373_32249.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4373_32249.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4373_32249.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4373_32249.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4373_32249.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4373_32249.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4373_32249.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4373_32249.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4373_32249.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4373_32249.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4373_32249.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4373_32249.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4373_32249.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4373_32249.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4373_32249.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4373_32249.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4373_32249.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4373_32249.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4373_32249.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4373_32249.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4373_32249.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4373_32249.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4373_32249.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4373_32249.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4373_32249.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4373_32249.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4373_32249.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4373_32249.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4373_32249.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4373_32249.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4373_32249.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4373_32249.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4373_32249.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4373_32249.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____32254 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32254
                                   then
                                     let uu____32259 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32261 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32263 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32265 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32259 uu____32261 uu____32263
                                       reason uu____32265
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4379_32272  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32279 =
                                             let uu____32289 =
                                               let uu____32297 =
                                                 let uu____32299 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32301 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32303 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32299 uu____32301
                                                   uu____32303
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32297, r)
                                                in
                                             [uu____32289]  in
                                           FStar_Errors.add_errors
                                             uu____32279);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32322 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32333  ->
                                               let uu____32334 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32336 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32338 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32334 uu____32336
                                                 reason uu____32338)) env2 g1
                                         true
                                        in
                                     match uu____32322 with
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
          let uu___4391_32346 = g  in
          let uu____32347 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4391_32346.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4391_32346.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4391_32346.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4391_32346.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32347
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32362 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32362
       then
         let uu____32367 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32367
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
      (let uu____32398 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32398
       then
         let uu____32403 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32403
       else ());
      (let solve_deferred_to_tactic g1 =
         let deferred = g1.FStar_TypeChecker_Common.deferred_to_tac  in
         match deferred with
         | [] -> g1
         | uu____32420 ->
             let prob_as_implicit uu____32431 =
               match uu____32431 with
               | (reason,prob) ->
                   (match prob with
                    | FStar_TypeChecker_Common.TProb tp when
                        tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ
                        ->
                        let uu____32444 =
                          env.FStar_TypeChecker_Env.type_of env
                            tp.FStar_TypeChecker_Common.lhs
                           in
                        (match uu____32444 with
                         | (uu____32451,tlhs,uu____32453) ->
                             let goal_ty =
                               let uu____32455 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   tlhs
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____32455 tlhs
                                 tp.FStar_TypeChecker_Common.lhs
                                 tp.FStar_TypeChecker_Common.rhs
                                in
                             let reason1 =
                               let uu____32458 =
                                 FStar_Util.string_of_int
                                   tp.FStar_TypeChecker_Common.pid
                                  in
                               Prims.op_Hat uu____32458
                                 (Prims.op_Hat ":" reason)
                                in
                             let uu____32461 =
                               FStar_TypeChecker_Env.new_implicit_var_aux
                                 reason1
                                 (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                 env goal_ty
                                 FStar_Syntax_Syntax.Allow_untyped
                                 FStar_Pervasives_Native.None
                                in
                             (match uu____32461 with
                              | (goal,ctx_uvar,uu____32476) ->
                                  let uu____32489 =
                                    let uu____32490 = FStar_List.hd ctx_uvar
                                       in
                                    FStar_Pervasives_Native.fst uu____32490
                                     in
                                  {
                                    FStar_TypeChecker_Common.imp_reason =
                                      reason1;
                                    FStar_TypeChecker_Common.imp_uvar =
                                      uu____32489;
                                    FStar_TypeChecker_Common.imp_tm = goal;
                                    FStar_TypeChecker_Common.imp_range =
                                      ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                  }))
                    | uu____32499 ->
                        failwith "Unexpected problem deferred to tactic")
                in
             let deferred_goals =
               FStar_List.map prob_as_implicit
                 g1.FStar_TypeChecker_Common.deferred_to_tac
                in
             let uu____32509 =
               FStar_List.partition
                 (fun imp  ->
                    let uu____32521 =
                      FStar_Syntax_Unionfind.find
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                       in
                    match uu____32521 with
                    | FStar_Pervasives_Native.None  -> true
                    | uu____32526 -> false)
                 g1.FStar_TypeChecker_Common.implicits
                in
             (match uu____32509 with
              | (more,imps) ->
                  let deferred_goals1 = FStar_List.append more deferred_goals
                     in
                  let guard =
                    let uu___4433_32544 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___4433_32544.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac = [];
                      FStar_TypeChecker_Common.deferred =
                        (uu___4433_32544.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___4433_32544.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = imps
                    }  in
                  let resolve_tac =
                    let uu____32551 =
                      FStar_TypeChecker_Env.lookup_attr env
                        FStar_Parser_Const.resolve_implicits_attr_string
                       in
                    match uu____32551 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let (uu____32554,lid::[]);
                        FStar_Syntax_Syntax.sigrng = uu____32556;
                        FStar_Syntax_Syntax.sigquals = uu____32557;
                        FStar_Syntax_Syntax.sigmeta = uu____32558;
                        FStar_Syntax_Syntax.sigattrs = uu____32559;
                        FStar_Syntax_Syntax.sigopts = uu____32560;_}::uu____32561
                        ->
                        let qn = FStar_TypeChecker_Env.lookup_qname env lid
                           in
                        let fv =
                          FStar_Syntax_Syntax.lid_as_fv lid
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_zero) FStar_Pervasives_Native.None
                           in
                        let dd =
                          let uu____32576 =
                            FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn
                             in
                          match uu____32576 with
                          | FStar_Pervasives_Native.Some dd -> dd
                          | FStar_Pervasives_Native.None  ->
                              failwith "Expected a dd"
                           in
                        let term =
                          let uu____32582 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Syntax_Syntax.fv_to_tm uu____32582  in
                        term
                    | uu____32583 -> failwith "Resolve_tac not found"  in
                  (env.FStar_TypeChecker_Env.try_solve_implicits_hook env
                     resolve_tac deferred_goals1;
                   guard))
          in
       let g1 = solve_deferred_constraints env g  in
       let g2 = solve_deferred_to_tactic g1  in
       let g3 = resolve_implicits env g2  in
       match g3.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____32591 = discharge_guard env g3  in
           FStar_All.pipe_left (fun a2  -> ()) uu____32591
       | imp::uu____32593 ->
           let uu____32596 =
             let uu____32602 =
               let uu____32604 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____32606 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____32604 uu____32606
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32602)
              in
           FStar_Errors.raise_error uu____32596
             imp.FStar_TypeChecker_Common.imp_range)
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32626 = teq env t1 t2  in
        force_trivial_guard env uu____32626
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32645 = teq_nosmt env t1 t2  in
        match uu____32645 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4478_32664 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4478_32664.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4478_32664.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4478_32664.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4478_32664.FStar_TypeChecker_Common.implicits)
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
        (let uu____32700 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32700
         then
           let uu____32705 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32707 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32705
             uu____32707
         else ());
        (let uu____32712 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32712 with
         | (prob,x,wl) ->
             let g =
               let uu____32731 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32742  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32731  in
             ((let uu____32764 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32764
               then
                 let uu____32769 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32771 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32773 =
                   let uu____32775 = FStar_Util.must g  in
                   guard_to_string env uu____32775  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32769 uu____32771 uu____32773
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
        let uu____32812 = check_subtyping env t1 t2  in
        match uu____32812 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32831 =
              let uu____32832 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32832 g  in
            FStar_Pervasives_Native.Some uu____32831
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32851 = check_subtyping env t1 t2  in
        match uu____32851 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32870 =
              let uu____32871 =
                let uu____32872 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32872]  in
              FStar_TypeChecker_Env.close_guard env uu____32871 g  in
            FStar_Pervasives_Native.Some uu____32870
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32910 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32910
         then
           let uu____32915 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32917 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32915
             uu____32917
         else ());
        (let uu____32922 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32922 with
         | (prob,x,wl) ->
             let g =
               let uu____32937 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32948  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32937  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32973 =
                      let uu____32974 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32974]  in
                    FStar_TypeChecker_Env.close_guard env uu____32973 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33015 = subtype_nosmt env t1 t2  in
        match uu____33015 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  