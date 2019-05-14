open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____86 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____157 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Env.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Dyn.dyn * FStar_Syntax_Syntax.term'
                  FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option
                  ->
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
                    let uu____1532 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____1532;
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
                       FStar_TypeChecker_Env.imp_reason = reason;
                       FStar_TypeChecker_Env.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Env.imp_tm = t;
                       FStar_TypeChecker_Env.imp_range = r
                     }  in
                   (ctx_uvar, t,
                     (let uu___71_1614 = wl  in
                      {
                        attempting = (uu___71_1614.attempting);
                        wl_deferred = (uu___71_1614.wl_deferred);
                        ctr = (uu___71_1614.ctr);
                        defer_ok = (uu___71_1614.defer_ok);
                        smt_ok = (uu___71_1614.smt_ok);
                        umax_heuristic_ok = (uu___71_1614.umax_heuristic_ok);
                        tcenv = (uu___71_1614.tcenv);
                        wl_implicits = (imp :: (wl.wl_implicits))
                      })))
  
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
            let uu___77_1835 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___77_1835.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___77_1835.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___77_1835.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___77_1835.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___77_1835.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___77_1835.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___77_1835.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___77_1835.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___77_1835.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___77_1835.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___77_1835.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___77_1835.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___77_1835.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___77_1835.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___77_1835.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___77_1835.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___77_1835.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___77_1835.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___77_1835.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___77_1835.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___77_1835.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___77_1835.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___77_1835.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___77_1835.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___77_1835.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___77_1835.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___77_1835.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___77_1835.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___77_1835.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___77_1835.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___77_1835.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___77_1835.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___77_1835.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___77_1835.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___77_1835.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___77_1835.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___77_1835.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___77_1835.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___77_1835.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___77_1835.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___77_1835.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___77_1835.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____2053 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____2053 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____2101 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____2137 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____2170 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____2181 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____2192 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_2251  ->
    match uu___0_2251 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____2271 = FStar_Syntax_Util.head_and_args t  in
    match uu____2271 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____2374 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____2376 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____2391 =
                     let uu____2393 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____2393  in
                   FStar_Util.format1 "@<%s>" uu____2391
                in
             let uu____2397 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____2374 uu____2376 uu____2397
         | uu____2400 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_2466  ->
      match uu___1_2466 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2540 =
            let uu____2544 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____2550 =
              let uu____2554 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____2560 =
                let uu____2564 =
                  let uu____2568 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____2568]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____2564
                 in
              uu____2554 :: uu____2560  in
            uu____2544 :: uu____2550  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____2540
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2602 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2608 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____2614 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____2602 uu____2608
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2614
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_2690  ->
      match uu___2_2690 with
      | UNIV (u,t) ->
          let x =
            let uu____2750 = FStar_Options.hide_uvar_nums ()  in
            if uu____2750
            then "?"
            else
              (let uu____2757 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____2757 FStar_Util.string_of_int)
             in
          let uu____2761 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____2761
      | TERM (u,t) ->
          let x =
            let uu____2792 = FStar_Options.hide_uvar_nums ()  in
            if uu____2792
            then "?"
            else
              (let uu____2799 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____2799 FStar_Util.string_of_int)
             in
          let uu____2803 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____2803
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____2930 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____2930 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____2961 =
      let uu____2965 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____2965
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____2961 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____3004 .
    (FStar_Syntax_Syntax.term * 'Auu____3004) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____3031 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____3060  ->
              match uu____3060 with
              | (x,uu____3071) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____3031 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____3366 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____3366
         then
           let uu____3371 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____3371
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_3382  ->
    match uu___3_3382 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____3388 .
    'Auu____3388 FStar_TypeChecker_Common.problem ->
      'Auu____3388 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___137_3433 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___137_3433.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___137_3433.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___137_3433.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___137_3433.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___137_3433.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___137_3433.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___137_3433.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____3452 .
    'Auu____3452 FStar_TypeChecker_Common.problem ->
      'Auu____3452 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_3505  ->
    match uu___4_3505 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _3545  -> FStar_TypeChecker_Common.TProb _3545)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _3585  -> FStar_TypeChecker_Common.CProb _3585)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_3591  ->
    match uu___5_3591 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___149_3612 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___149_3612.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___149_3612.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___149_3612.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___149_3612.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___149_3612.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___149_3612.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___149_3612.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___149_3612.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___149_3612.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___153_3690 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___153_3690.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___153_3690.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___153_3690.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___153_3690.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___153_3690.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___153_3690.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___153_3690.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___153_3690.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___153_3690.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_3758  ->
      match uu___6_3758 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_3765  ->
    match uu___7_3765 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_3816  ->
    match uu___8_3816 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_3869  ->
    match uu___9_3869 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_3922  ->
    match uu___10_3922 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_3979  ->
    match uu___11_3979 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_4048  ->
    match uu___12_4048 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_4126  ->
    match uu___13_4126 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____4188 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____4188) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____4228 =
          let uu____4230 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____4230  in
        if uu____4228
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____4292)::bs ->
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
          let uu____4409 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____4463 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____4463]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____4409
      | FStar_TypeChecker_Common.CProb p ->
          let uu____4530 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____4584 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____4584]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____4530
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____4663 =
          let uu____4665 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____4665  in
        if uu____4663
        then ()
        else
          (let uu____4670 =
             let uu____4678 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____4678
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____4670 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____4765 =
          let uu____4767 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____4767  in
        if uu____4765
        then ()
        else
          (let uu____4772 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____4772)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____4805 =
        let uu____4807 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____4807  in
      if uu____4805
      then ()
      else
        (let msgf m =
           let uu____4821 =
             let uu____4823 =
               let uu____4825 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____4825 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____4823  in
           Prims.op_Hat msg uu____4821  in
         (let uu____4830 = msgf "scope"  in
          let uu____4833 = p_scope prob  in
          def_scope_wf uu____4830 (p_loc prob) uu____4833);
         (let uu____4850 = msgf "guard"  in
          def_check_scoped uu____4850 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____4872 = msgf "lhs"  in
                def_check_scoped uu____4872 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____4879 = msgf "rhs"  in
                def_check_scoped uu____4879 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____4905 = msgf "lhs"  in
                def_check_scoped_comp uu____4905 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____4912 = msgf "rhs"  in
                def_check_scoped_comp uu____4912 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___246_4977 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___246_4977.wl_deferred);
          ctr = (uu___246_4977.ctr);
          defer_ok = (uu___246_4977.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___246_4977.umax_heuristic_ok);
          tcenv = (uu___246_4977.tcenv);
          wl_implicits = (uu___246_4977.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____5001 .
    FStar_TypeChecker_Env.env ->
      ('Auu____5001 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___250_5140 = empty_worklist env  in
      let uu____5157 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____5157;
        wl_deferred = (uu___250_5140.wl_deferred);
        ctr = (uu___250_5140.ctr);
        defer_ok = (uu___250_5140.defer_ok);
        smt_ok = (uu___250_5140.smt_ok);
        umax_heuristic_ok = (uu___250_5140.umax_heuristic_ok);
        tcenv = (uu___250_5140.tcenv);
        wl_implicits = (uu___250_5140.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___255_5220 = wl  in
        {
          attempting = (uu___255_5220.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___255_5220.ctr);
          defer_ok = (uu___255_5220.defer_ok);
          smt_ok = (uu___255_5220.smt_ok);
          umax_heuristic_ok = (uu___255_5220.umax_heuristic_ok);
          tcenv = (uu___255_5220.tcenv);
          wl_implicits = (uu___255_5220.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___260_5288 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___260_5288.wl_deferred);
         ctr = (uu___260_5288.ctr);
         defer_ok = (uu___260_5288.defer_ok);
         smt_ok = (uu___260_5288.smt_ok);
         umax_heuristic_ok = (uu___260_5288.umax_heuristic_ok);
         tcenv = (uu___260_5288.tcenv);
         wl_implicits = (uu___260_5288.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____5318 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____5318 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____5504 = FStar_Syntax_Util.type_u ()  in
            match uu____5504 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____5540 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____5540 with
                 | (uu____5594,tt,wl1) ->
                     let uu____5637 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____5637, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_5663  ->
    match uu___14_5663 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _5699  -> FStar_TypeChecker_Common.TProb _5699) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _5739  -> FStar_TypeChecker_Common.CProb _5739) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____5751 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____5751 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____5771  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____5813 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____5813 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____5813 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____5813 FStar_TypeChecker_Common.problem *
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
                        let uu____5980 =
                          let uu____5994 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5994]  in
                        FStar_List.append scope uu____5980
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____6067 =
                      let uu____6070 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____6070  in
                    FStar_List.append uu____6067
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____6104 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____6104 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____6224 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____6224;
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
                  (let uu____6377 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____6377 with
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
                  (let uu____6614 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____6614 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____6741 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____6741 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____6741 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____6741 FStar_TypeChecker_Common.problem *
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
                          let uu____6994 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____6994]  in
                        let uu____7028 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____7028
                     in
                  let uu____7039 =
                    let uu____7066 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___343_7082 = wl  in
                       {
                         attempting = (uu___343_7082.attempting);
                         wl_deferred = (uu___343_7082.wl_deferred);
                         ctr = (uu___343_7082.ctr);
                         defer_ok = (uu___343_7082.defer_ok);
                         smt_ok = (uu___343_7082.smt_ok);
                         umax_heuristic_ok =
                           (uu___343_7082.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___343_7082.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____7066
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____7039 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____7206 =
                              let uu____7211 =
                                let uu____7212 =
                                  let uu____7225 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____7225
                                   in
                                [uu____7212]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____7211  in
                            uu____7206 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____7288 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____7288;
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
                let uu____7411 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____7411;
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
  'Auu____7430 .
    worklist ->
      'Auu____7430 FStar_TypeChecker_Common.problem ->
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
              let uu____7527 =
                let uu____7530 =
                  let uu____7531 =
                    let uu____7547 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____7547)  in
                  FStar_Syntax_Syntax.NT uu____7531  in
                [uu____7530]  in
              FStar_Syntax_Subst.subst uu____7527 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____7696 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____7696
        then
          let uu____7704 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____7707 = prob_to_string env d  in
          let uu____7709 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____7704 uu____7707 uu____7709 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____7725 -> failwith "impossible"  in
           let uu____7728 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____7759 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____7765 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____7759, uu____7765)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____7791 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____7797 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____7791, uu____7797)
              in
           match uu____7728 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_7829  ->
            match uu___15_7829 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____7843 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____7871 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____7871 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_7930  ->
           match uu___16_7930 with
           | UNIV uu____7937 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____7972 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____7972
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
        (fun uu___17_8012  ->
           match uu___17_8012 with
           | UNIV (u',t) ->
               let uu____8017 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____8017
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____8024 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____8156 =
        let uu____8165 =
          let uu____8174 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____8174
           in
        FStar_Syntax_Subst.compress uu____8165  in
      FStar_All.pipe_right uu____8156 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____8322 =
        let uu____8331 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____8331  in
      FStar_All.pipe_right uu____8322 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8363 = FStar_Syntax_Util.head_and_args t  in
    match uu____8363 with
    | (h,uu____8390) ->
        let uu____8431 =
          let uu____8432 = FStar_Syntax_Subst.compress h  in
          uu____8432.FStar_Syntax_Syntax.n  in
        (match uu____8431 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____8445 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____8578 = should_strongly_reduce t  in
      if uu____8578
      then
        let uu____8585 =
          let uu____8594 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____8594  in
        FStar_All.pipe_right uu____8585 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____8620 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____8620) ->
        (FStar_Syntax_Syntax.term * 'Auu____8620)
  =
  fun env  ->
    fun t  ->
      let uu____8763 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____8763, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____8968  ->
              match uu____8968 with
              | (x,imp) ->
                  let uu____9007 =
                    let uu___440_9018 = x  in
                    let uu____9029 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___440_9018.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___440_9018.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____9029
                    }  in
                  (uu____9007, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____9082 = aux u3  in FStar_Syntax_Syntax.U_succ uu____9082
        | FStar_Syntax_Syntax.U_max us ->
            let uu____9086 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____9086
        | uu____9089 -> u2  in
      let uu____9090 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____9090
  
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
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____9564 = norm_refinement env t12  in
                 match uu____9564 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____9600;
                     FStar_Syntax_Syntax.vars = uu____9601;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____9682 =
                       let uu____9684 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____9686 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____9684 uu____9686
                        in
                     failwith uu____9682)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____9719 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____9719
          | FStar_Syntax_Syntax.Tm_uinst uu____9728 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____9812 =
                   let uu____9813 = FStar_Syntax_Subst.compress t1'  in
                   uu____9813.FStar_Syntax_Syntax.n  in
                 match uu____9812 with
                 | FStar_Syntax_Syntax.Tm_refine uu____9849 -> aux true t1'
                 | uu____9866 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____9903 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____9980 =
                   let uu____9981 = FStar_Syntax_Subst.compress t1'  in
                   uu____9981.FStar_Syntax_Syntax.n  in
                 match uu____9980 with
                 | FStar_Syntax_Syntax.Tm_refine uu____10017 -> aux true t1'
                 | uu____10034 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____10071 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____10169 =
                   let uu____10170 = FStar_Syntax_Subst.compress t1'  in
                   uu____10170.FStar_Syntax_Syntax.n  in
                 match uu____10169 with
                 | FStar_Syntax_Syntax.Tm_refine uu____10206 -> aux true t1'
                 | uu____10223 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____10260 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____10297 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____10334 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____10376 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____10418 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____10478 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____10549 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____10598 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____10655 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____10716 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____10790 ->
              let uu____10801 =
                let uu____10803 = FStar_Syntax_Print.term_to_string t12  in
                let uu____10805 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____10803 uu____10805
                 in
              failwith uu____10801
          | FStar_Syntax_Syntax.Tm_ascribed uu____10833 ->
              let uu____10880 =
                let uu____10882 = FStar_Syntax_Print.term_to_string t12  in
                let uu____10884 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____10882 uu____10884
                 in
              failwith uu____10880
          | FStar_Syntax_Syntax.Tm_delayed uu____10912 ->
              let uu____10943 =
                let uu____10945 = FStar_Syntax_Print.term_to_string t12  in
                let uu____10947 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____10945 uu____10947
                 in
              failwith uu____10943
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____10975 =
                let uu____10977 = FStar_Syntax_Print.term_to_string t12  in
                let uu____10979 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____10977 uu____10979
                 in
              failwith uu____10975
           in
        let uu____11007 = whnf env t1  in aux false uu____11007
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____11466 = base_and_refinement env t  in
      FStar_All.pipe_right uu____11466 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____11576 = FStar_Syntax_Syntax.null_bv t  in
    (uu____11576, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____11756 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____11756 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____11935  ->
    match uu____11935 with
    | (t_base,refopt) ->
        let uu____12013 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____12013 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____12181 =
      let uu____12185 =
        let uu____12188 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____12215  ->
                  match uu____12215 with | (uu____12224,uu____12225,x) -> x))
           in
        FStar_List.append wl.attempting uu____12188  in
      FStar_List.map (wl_prob_to_string wl) uu____12185  in
    FStar_All.pipe_right uu____12181 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____12260 .
    ('Auu____12260 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____12280  ->
    match uu____12280 with
    | (uu____12295,c,args) ->
        let uu____12314 = print_ctx_uvar c  in
        let uu____12316 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____12314 uu____12316
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____12334 = FStar_Syntax_Util.head_and_args t  in
    match uu____12334 with
    | (head1,_args) ->
        let uu____12402 =
          let uu____12403 = FStar_Syntax_Subst.compress head1  in
          uu____12403.FStar_Syntax_Syntax.n  in
        (match uu____12402 with
         | FStar_Syntax_Syntax.Tm_uvar uu____12415 -> true
         | uu____12437 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____12461 = FStar_Syntax_Util.head_and_args t  in
    match uu____12461 with
    | (head1,_args) ->
        let uu____12536 =
          let uu____12537 = FStar_Syntax_Subst.compress head1  in
          uu____12537.FStar_Syntax_Syntax.n  in
        (match uu____12536 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____12557) -> u
         | uu____12590 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____12663 = FStar_Syntax_Util.head_and_args t  in
      match uu____12663 with
      | (head1,args) ->
          let uu____12742 =
            let uu____12743 = FStar_Syntax_Subst.compress head1  in
            uu____12743.FStar_Syntax_Syntax.n  in
          (match uu____12742 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____12767)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____12852 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_12877  ->
                         match uu___18_12877 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____12903 =
                               let uu____12904 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____12904.FStar_Syntax_Syntax.n  in
                             (match uu____12903 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____12922 -> false)
                         | uu____12924 -> true))
                  in
               (match uu____12852 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____12962 =
                        FStar_List.collect
                          (fun uu___19_12979  ->
                             match uu___19_12979 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____12988 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____12988]
                             | uu____12989 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____12962 FStar_List.rev  in
                    let uu____13027 =
                      let uu____13054 =
                        let uu____13068 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_13100  ->
                                  match uu___20_13100 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____13109 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____13109]
                                  | uu____13110 -> []))
                           in
                        FStar_All.pipe_right uu____13068 FStar_List.rev  in
                      let uu____13148 =
                        let uu____13159 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____13159  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____13054 uu____13148
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____13027 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____13264  ->
                                match uu____13264 with
                                | (x,i) ->
                                    let uu____13302 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____13302, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____13365  ->
                                match uu____13365 with
                                | (a,i) ->
                                    let uu____13400 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____13400, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v1, all_args), wl1))))
           | uu____13470 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____13524 =
          let uu____13560 =
            let uu____13561 = FStar_Syntax_Subst.compress k  in
            uu____13561.FStar_Syntax_Syntax.n  in
          match uu____13560 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____13705 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____13705)
              else
                (let uu____13766 = FStar_Syntax_Util.abs_formals t  in
                 match uu____13766 with
                 | (ys',t1,uu____13823) ->
                     let uu____13850 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____13850))
          | uu____13920 ->
              let uu____13921 =
                let uu____13930 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____13930)  in
              ((ys, t), uu____13921)
           in
        match uu____13524 with
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
                 let uu____14140 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____14140 c  in
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
               (let uu____14305 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____14305
                then
                  let uu____14310 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____14312 = print_ctx_uvar uv  in
                  let uu____14314 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____14310 uu____14312 uu____14314
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____14338 =
                   let uu____14340 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____14340  in
                 let uu____14343 =
                   let uu____14351 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____14351
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____14338 uu____14343 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____14430 =
               let uu____14431 =
                 let uu____14433 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____14435 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____14433 uu____14435
                  in
               failwith uu____14431  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____14532  ->
                       match uu____14532 with
                       | (a,i) ->
                           let uu____14570 =
                             let uu____14571 = FStar_Syntax_Subst.compress a
                                in
                             uu____14571.FStar_Syntax_Syntax.n  in
                           (match uu____14570 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____14630 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____14669 =
                 let uu____14671 = is_flex g  in
                 Prims.op_Negation uu____14671  in
               if uu____14669
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____14696 = destruct_flex_t g wl  in
                  match uu____14696 with
                  | ((uu____14717,uv1,args),wl1) ->
                      ((let uu____14762 = args_as_binders args  in
                        assign_solution uu____14762 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___692_14764 = wl1  in
              {
                attempting = (uu___692_14764.attempting);
                wl_deferred = (uu___692_14764.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___692_14764.defer_ok);
                smt_ok = (uu___692_14764.smt_ok);
                umax_heuristic_ok = (uu___692_14764.umax_heuristic_ok);
                tcenv = (uu___692_14764.tcenv);
                wl_implicits = (uu___692_14764.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____14829 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____14829
         then
           let uu____14834 = FStar_Util.string_of_int pid  in
           let uu____14836 =
             let uu____14838 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____14838 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____14834
             uu____14836
         else ());
        commit sol;
        (let uu___700_14852 = wl  in
         {
           attempting = (uu___700_14852.attempting);
           wl_deferred = (uu___700_14852.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___700_14852.defer_ok);
           smt_ok = (uu___700_14852.smt_ok);
           umax_heuristic_ok = (uu___700_14852.umax_heuristic_ok);
           tcenv = (uu___700_14852.tcenv);
           wl_implicits = (uu___700_14852.wl_implicits)
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
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____14998,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____15066 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____15066
              in
           (let uu____15084 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____15084
            then
              let uu____15089 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____15093 =
                let uu____15095 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____15095 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____15089
                uu____15093
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____15170 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____15170 FStar_Util.set_elements  in
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
      let uu____15306 = occurs uk t  in
      match uu____15306 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____15377 =
                 let uu____15379 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____15381 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____15379 uu____15381
                  in
               FStar_Pervasives_Native.Some uu____15377)
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
            let uu____15569 = maximal_prefix bs_tail bs'_tail  in
            (match uu____15569 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____15635 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____15712  ->
             match uu____15712 with
             | (x,uu____15729) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____15757 = FStar_List.last bs  in
      match uu____15757 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____15796) ->
          let uu____15822 =
            FStar_Util.prefix_until
              (fun uu___21_15837  ->
                 match uu___21_15837 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____15845 -> false) g
             in
          (match uu____15822 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____15859,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____15952 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____15952 with
        | (pfx,uu____15970) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____15982 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____15982 with
             | (uu____16018,src',wl1) ->
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
                 | uu____16334 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____16335 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____16439  ->
                  fun uu____16440  ->
                    match (uu____16439, uu____16440) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____16628 =
                          let uu____16630 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____16630
                           in
                        if uu____16628
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____16694 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____16694
                           then
                             let uu____16726 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____16726)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____16335 with | (isect,uu____16831) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____16892 'Auu____16893 .
    (FStar_Syntax_Syntax.bv * 'Auu____16892) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____16893) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____16991  ->
              fun uu____16992  ->
                match (uu____16991, uu____16992) with
                | ((a,uu____17031),(b,uu____17033)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____17079 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____17079) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____17135  ->
           match uu____17135 with
           | (y,uu____17147) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____17167 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____17167) Prims.list ->
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
                   let uu____17531 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____17531
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____17584 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____17646 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____17690 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____17711 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_17719  ->
    match uu___22_17719 with
    | MisMatch (d1,d2) ->
        let uu____17731 =
          let uu____17733 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____17735 =
            let uu____17737 =
              let uu____17739 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____17739 ")"  in
            Prims.op_Hat ") (" uu____17737  in
          Prims.op_Hat uu____17733 uu____17735  in
        Prims.op_Hat "MisMatch (" uu____17731
    | HeadMatch u ->
        let uu____17746 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____17746
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_17755  ->
    match uu___23_17755 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____17772 -> HeadMatch false
  
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
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
          let uu____17912 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____17912 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____17935 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____18087 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____18101 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____18140 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____18140
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____18149 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____18155 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____18161 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____18182 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____18207 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____18246) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____18260,uu____18261) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____18343) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____18384;
             FStar_Syntax_Syntax.index = uu____18385;
             FStar_Syntax_Syntax.sort = t2;_},uu____18387)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____18414 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____18415 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____18416 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____18440 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____18453 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____18492 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____18492
  
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
           { FStar_Syntax_Syntax.blob = uu____18651;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____18652;
             FStar_Syntax_Syntax.ltyp = uu____18653;
             FStar_Syntax_Syntax.rng = uu____18654;_},uu____18655)
            ->
            let uu____18674 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____18674 t21
        | (uu____18683,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____18684;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____18685;
             FStar_Syntax_Syntax.ltyp = uu____18686;
             FStar_Syntax_Syntax.rng = uu____18687;_})
            ->
            let uu____18706 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____18706
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____18742 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____18742
            then FullMatch
            else
              (let uu____18747 =
                 let uu____18756 =
                   let uu____18759 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____18759  in
                 let uu____18760 =
                   let uu____18763 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____18763  in
                 (uu____18756, uu____18760)  in
               MisMatch uu____18747)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____18769),FStar_Syntax_Syntax.Tm_uinst (g,uu____18771)) ->
            let uu____18796 = head_matches env f g  in
            FStar_All.pipe_right uu____18796 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____18797) -> HeadMatch true
        | (uu____18799,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____18803 = FStar_Const.eq_const c d  in
            if uu____18803
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____18813),FStar_Syntax_Syntax.Tm_uvar (uv',uu____18815)) ->
            let uu____18880 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____18880
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____18890),FStar_Syntax_Syntax.Tm_refine (y,uu____18892)) ->
            let uu____18937 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____18937 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____18939),uu____18940) ->
            let uu____18963 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____18963 head_match
        | (uu____18964,FStar_Syntax_Syntax.Tm_refine (x,uu____18966)) ->
            let uu____18989 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____18989 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____18990,FStar_Syntax_Syntax.Tm_type uu____18991) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____18993,FStar_Syntax_Syntax.Tm_arrow uu____18994) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____19043),FStar_Syntax_Syntax.Tm_app
           (head',uu____19045)) ->
            let uu____19126 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____19126 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____19128),uu____19129) ->
            let uu____19170 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____19170 head_match
        | (uu____19171,FStar_Syntax_Syntax.Tm_app (head1,uu____19173)) ->
            let uu____19214 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____19214 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____19215,FStar_Syntax_Syntax.Tm_let
           uu____19216) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____19266,FStar_Syntax_Syntax.Tm_match uu____19267) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____19343,FStar_Syntax_Syntax.Tm_abs
           uu____19344) -> HeadMatch true
        | uu____19414 ->
            let uu____19419 =
              let uu____19428 = delta_depth_of_term env t11  in
              let uu____19431 = delta_depth_of_term env t21  in
              (uu____19428, uu____19431)  in
            MisMatch uu____19419
  
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
              let uu____19676 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____19676  in
            (let uu____19686 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____19686
             then
               let uu____19691 = FStar_Syntax_Print.term_to_string t  in
               let uu____19693 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____19691 uu____19693
             else ());
            (let uu____19698 =
               let uu____19699 = FStar_Syntax_Util.un_uinst head1  in
               uu____19699.FStar_Syntax_Syntax.n  in
             match uu____19698 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____19720 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____19720 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____19750 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____19750
                        then
                          let uu____19755 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____19755
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____19764 ->
                      let basic_steps =
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
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
                        FStar_TypeChecker_Normalize.normalize steps env t  in
                      let uu____19797 =
                        let uu____19799 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____19799 = FStar_Syntax_Util.Equal  in
                      if uu____19797
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____19814 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____19814
                          then
                            let uu____19819 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____19821 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____19819 uu____19821
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____19830 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____20138 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____20138
             then
               let uu____20143 = FStar_Syntax_Print.term_to_string t11  in
               let uu____20145 = FStar_Syntax_Print.term_to_string t21  in
               let uu____20147 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____20143
                 uu____20145 uu____20147
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____20183 =
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
               match uu____20183 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____20311 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____20311 with
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
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > (Prims.parse_int "0")) || (j > (Prims.parse_int "0")))
                   && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____20381),uu____20382)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____20411 =
                      let uu____20428 = maybe_inline t11  in
                      let uu____20435 = maybe_inline t21  in
                      (uu____20428, uu____20435)  in
                    match uu____20411 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t22)
             | MisMatch
                 (uu____20578,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____20579))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____20608 =
                      let uu____20625 = maybe_inline t11  in
                      let uu____20632 = maybe_inline t21  in
                      (uu____20625, uu____20632)  in
                    match uu____20608 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____20787 -> fail1 n_delta r t11 t21
             | uu____20796 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____20819 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____20819
           then
             let uu____20824 = FStar_Syntax_Print.term_to_string t1  in
             let uu____20826 = FStar_Syntax_Print.term_to_string t2  in
             let uu____20828 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____20844 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____20877 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____20877
                    (fun uu____20960  ->
                       match uu____20960 with
                       | (t11,t21) ->
                           let uu____20992 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____20994 =
                             let uu____20996 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____20996  in
                           Prims.op_Hat uu____20992 uu____20994))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____20824 uu____20826 uu____20828 uu____20844
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____21017 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____21017 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_21048  ->
    match uu___24_21048 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> (Prims.parse_int "0")
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> (Prims.parse_int "1")
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.parse_int "2")
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.parse_int "3")
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.parse_int "4")
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.parse_int "5")
  
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
      let uu___1204_21239 = p  in
      let uu____21257 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____21270 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1204_21239.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____21257;
        FStar_TypeChecker_Common.relation =
          (uu___1204_21239.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____21270;
        FStar_TypeChecker_Common.element =
          (uu___1204_21239.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1204_21239.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1204_21239.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1204_21239.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1204_21239.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1204_21239.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____21456 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____21456
            (fun _21491  -> FStar_TypeChecker_Common.TProb _21491)
      | FStar_TypeChecker_Common.CProb uu____21492 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____21638 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____21638 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____21661 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____21661 with
           | (lh,lhs_args) ->
               let uu____21736 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____21736 with
                | (rh,rhs_args) ->
                    let uu____21811 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____21854,FStar_Syntax_Syntax.Tm_uvar uu____21855)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____22018 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____22068,uu____22069)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____22111,FStar_Syntax_Syntax.Tm_uvar uu____22112)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____22154,FStar_Syntax_Syntax.Tm_arrow
                         uu____22155) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1255_22217 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1255_22217.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1255_22217.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1255_22217.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1255_22217.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1255_22217.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1255_22217.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1255_22217.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1255_22217.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1255_22217.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____22275,FStar_Syntax_Syntax.Tm_type uu____22276)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1255_22315 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1255_22315.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1255_22315.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1255_22315.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1255_22315.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1255_22315.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1255_22315.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1255_22315.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1255_22315.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1255_22315.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____22373,FStar_Syntax_Syntax.Tm_uvar uu____22374)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1255_22413 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1255_22413.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1255_22413.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1255_22413.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1255_22413.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1255_22413.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1255_22413.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1255_22413.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1255_22413.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1255_22413.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____22471,FStar_Syntax_Syntax.Tm_uvar uu____22472)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____22510,uu____22511)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____22549,FStar_Syntax_Syntax.Tm_uvar uu____22550)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____22588,uu____22589) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____21811 with
                     | (rank,tp1) ->
                         let uu____22647 =
                           FStar_All.pipe_right
                             (let uu___1275_22666 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1275_22666.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1275_22666.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1275_22666.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1275_22666.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1275_22666.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1275_22666.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1275_22666.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1275_22666.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1275_22666.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _22724  ->
                                FStar_TypeChecker_Common.TProb _22724)
                            in
                         (rank, uu____22647))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____22743 =
            FStar_All.pipe_right
              (let uu___1279_22762 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1279_22762.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1279_22762.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1279_22762.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1279_22762.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1279_22762.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1279_22762.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1279_22762.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1279_22762.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1279_22762.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _22820  -> FStar_TypeChecker_Common.CProb _22820)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____22743)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____22896 probs =
      match uu____22896 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____22977 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____22998 = rank wl.tcenv hd1  in
               (match uu____22998 with
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
                      (let uu____23059 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____23064 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____23064)
                          in
                       if uu____23059
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
          let uu____23253 = FStar_Syntax_Util.head_and_args t  in
          match uu____23253 with
          | (hd1,uu____23280) ->
              let uu____23321 =
                let uu____23322 = FStar_Syntax_Subst.compress hd1  in
                uu____23322.FStar_Syntax_Syntax.n  in
              (match uu____23321 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____23335) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____23396  ->
                           match uu____23396 with
                           | (y,uu____23410) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____23453  ->
                                       match uu____23453 with
                                       | (x,uu____23467) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____23482 -> false)
           in
        let uu____23484 = rank tcenv p  in
        match uu____23484 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____23493 -> true
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
  | UFailed of Prims.string 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____23604 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____23671 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____23731 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
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
                        let uu____23809 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____23809 with
                        | (k,uu____23817) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____23832 -> false)))
            | uu____23834 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____23886 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____23894 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____23894 = (Prims.parse_int "0")))
                           in
                        if uu____23886 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____23915 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____23923 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____23923 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____23915)
               in
            let uu____23927 = filter1 u12  in
            let uu____23930 = filter1 u22  in (uu____23927, uu____23930)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____23965 = filter_out_common_univs us1 us2  in
                   (match uu____23965 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____24041 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____24041 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____24052 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____24063 =
                             let uu____24065 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____24067 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____24065 uu____24067
                              in
                           UFailed uu____24063))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____24109 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____24109 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____24159 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____24159 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____24170 ->
                   let uu____24175 =
                     let uu____24177 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____24179 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____24177 uu____24179 msg
                      in
                   UFailed uu____24175)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____24182,uu____24183) ->
              let uu____24185 =
                let uu____24187 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____24189 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____24187 uu____24189
                 in
              failwith uu____24185
          | (FStar_Syntax_Syntax.U_unknown ,uu____24192) ->
              let uu____24193 =
                let uu____24195 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____24197 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____24195 uu____24197
                 in
              failwith uu____24193
          | (uu____24200,FStar_Syntax_Syntax.U_bvar uu____24201) ->
              let uu____24203 =
                let uu____24205 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____24207 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____24205 uu____24207
                 in
              failwith uu____24203
          | (uu____24210,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____24211 =
                let uu____24213 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____24215 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____24213 uu____24215
                 in
              failwith uu____24211
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____24253 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____24253
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____24288 = occurs_univ v1 u3  in
              if uu____24288
              then
                let uu____24291 =
                  let uu____24293 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____24295 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____24293 uu____24295
                   in
                try_umax_components u11 u21 uu____24291
              else
                (let uu____24300 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____24300)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____24330 = occurs_univ v1 u3  in
              if uu____24330
              then
                let uu____24333 =
                  let uu____24335 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____24337 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____24335 uu____24337
                   in
                try_umax_components u11 u21 uu____24333
              else
                (let uu____24342 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____24342)
          | (FStar_Syntax_Syntax.U_max uu____24359,uu____24360) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____24368 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____24368
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____24374,FStar_Syntax_Syntax.U_max uu____24375) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____24383 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____24383
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____24389,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____24391,FStar_Syntax_Syntax.U_name uu____24392) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____24396) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____24398) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____24402,FStar_Syntax_Syntax.U_succ uu____24403) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____24407,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
  
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
      let uu____24532 = bc1  in
      match uu____24532 with
      | (bs1,mk_cod1) ->
          let uu____24576 = bc2  in
          (match uu____24576 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____24687 = aux xs ys  in
                     (match uu____24687 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____24770 =
                       let uu____24777 = mk_cod1 xs  in ([], uu____24777)  in
                     let uu____24780 =
                       let uu____24787 = mk_cod2 ys  in ([], uu____24787)  in
                     (uu____24770, uu____24780)
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
                  let uu____25058 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____25058 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____25084 =
                    let uu____25093 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____25093 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____25084
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____25122 = has_type_guard t1 t2  in (uu____25122, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____25143 = has_type_guard t2 t1  in (uu____25143, wl)
  
let is_flex_pat :
  'Auu____25173 'Auu____25174 'Auu____25175 .
    ('Auu____25173 * 'Auu____25174 * 'Auu____25175 Prims.list) -> Prims.bool
  =
  fun uu___25_25189  ->
    match uu___25_25189 with
    | (uu____25198,uu____25199,[]) -> true
    | uu____25203 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____25352 = f  in
      match uu____25352 with
      | (uu____25363,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____25364;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____25365;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____25368;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____25369;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____25370;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____25371;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____25501  ->
                 match uu____25501 with
                 | (y,uu____25515) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____25760 =
                  let uu____25784 =
                    let uu____25795 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____25795  in
                  ((FStar_List.rev pat_binders), uu____25784)  in
                FStar_Pervasives_Native.Some uu____25760
            | (uu____25859,[]) ->
                let uu____25908 =
                  let uu____25932 =
                    let uu____25943 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____25943  in
                  ((FStar_List.rev pat_binders), uu____25932)  in
                FStar_Pervasives_Native.Some uu____25908
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____26110 =
                  let uu____26111 = FStar_Syntax_Subst.compress a  in
                  uu____26111.FStar_Syntax_Syntax.n  in
                (match uu____26110 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____26153 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____26153
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1603_26212 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1603_26212.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1603_26212.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____26226 =
                            let uu____26227 =
                              let uu____26243 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____26243)  in
                            FStar_Syntax_Syntax.NT uu____26227  in
                          [uu____26226]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1609_26294 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1609_26294.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1609_26294.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____26305 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____26373 =
                  let uu____26397 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____26397  in
                (match uu____26373 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____26530 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____26589 ->
               let uu____26590 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____26590 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____28045 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____28045
       then
         let uu____28050 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____28050
       else ());
      (let uu____28055 = next_prob probs  in
       match uu____28055 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1634_28098 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1634_28098.wl_deferred);
               ctr = (uu___1634_28098.ctr);
               defer_ok = (uu___1634_28098.defer_ok);
               smt_ok = (uu___1634_28098.smt_ok);
               umax_heuristic_ok = (uu___1634_28098.umax_heuristic_ok);
               tcenv = (uu___1634_28098.tcenv);
               wl_implicits = (uu___1634_28098.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____28157 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____28157
                 then
                   let uu____28172 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____28172
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
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1646_28208 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1646_28208.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1646_28208.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1646_28208.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1646_28208.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1646_28208.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1646_28208.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1646_28208.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1646_28208.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1646_28208.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____28289 ->
                let uu____28300 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____28371  ->
                          match uu____28371 with
                          | (c,uu____28382,uu____28383) -> c < probs.ctr))
                   in
                (match uu____28300 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____28438 =
                            let uu____28443 =
                              FStar_List.map
                                (fun uu____28461  ->
                                   match uu____28461 with
                                   | (uu____28475,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____28443, (probs.wl_implicits))  in
                          Success uu____28438
                      | uu____28483 ->
                          let uu____28494 =
                            let uu___1664_28511 = probs  in
                            let uu____28528 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____28551  ->
                                      match uu____28551 with
                                      | (uu____28560,uu____28561,y) -> y))
                               in
                            {
                              attempting = uu____28528;
                              wl_deferred = rest;
                              ctr = (uu___1664_28511.ctr);
                              defer_ok = (uu___1664_28511.defer_ok);
                              smt_ok = (uu___1664_28511.smt_ok);
                              umax_heuristic_ok =
                                (uu___1664_28511.umax_heuristic_ok);
                              tcenv = (uu___1664_28511.tcenv);
                              wl_implicits = (uu___1664_28511.wl_implicits)
                            }  in
                          solve env uu____28494))))

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
            let uu____28634 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____28634 with
            | USolved wl1 ->
                let uu____28644 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____28644
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

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
                  let uu____28812 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____28812 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____28823 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____28852;
                  FStar_Syntax_Syntax.vars = uu____28853;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____28856;
                  FStar_Syntax_Syntax.vars = uu____28857;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____28892,uu____28893) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____28905,FStar_Syntax_Syntax.Tm_uinst uu____28906) ->
                failwith "Impossible: expect head symbols to match"
            | uu____28918 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____28992 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____28992
              then
                let uu____28997 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____28997 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

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
               let uu____29359 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____29359 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____29552 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____29552
                then
                  let uu____29557 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____29559 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____29557 uu____29559
                else ());
               (let uu____29564 = head_matches_delta env1 wl2 t1 t2  in
                match uu____29564 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____29658 = eq_prob t1 t2 wl2  in
                         (match uu____29658 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____29727 ->
                         let uu____29736 = eq_prob t1 t2 wl2  in
                         (match uu____29736 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____29902 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____29957 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____29966 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____29957, uu____29966)
                           | FStar_Pervasives_Native.None  ->
                               let uu____29995 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____30004 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____29995, uu____30004)
                            in
                         (match uu____29902 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____30119 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____30119 with
                                | (t1_hd,t1_args) ->
                                    let uu____30196 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____30196 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____30318 =
                                              let uu____30333 =
                                                let uu____30348 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____30348 :: t1_args  in
                                              let uu____30373 =
                                                let uu____30386 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____30386 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____30459  ->
                                                   fun uu____30460  ->
                                                     fun uu____30461  ->
                                                       match (uu____30459,
                                                               uu____30460,
                                                               uu____30461)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____30551),
                                                          (a2,uu____30553))
                                                           ->
                                                           let uu____30638 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____30638
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____30333
                                                uu____30373
                                               in
                                            match uu____30318 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1818_30752 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1818_30752.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1818_30752.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1818_30752.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____30784 =
                                                  solve env1 wl'  in
                                                (match uu____30784 with
                                                 | Success (uu____30795,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1827_30807
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1827_30807.attempting);
                                                            wl_deferred =
                                                              (uu___1827_30807.wl_deferred);
                                                            ctr =
                                                              (uu___1827_30807.ctr);
                                                            defer_ok =
                                                              (uu___1827_30807.defer_ok);
                                                            smt_ok =
                                                              (uu___1827_30807.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1827_30807.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1827_30807.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____30828 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____30913 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____30913 with
                                | (t1_base,p1_opt) ->
                                    let uu____31000 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____31000 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____31220 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____31220
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
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____31402 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____31402
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____31519 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____31519
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____31636 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____31636
                                           | uu____31647 -> t_base  in
                                         let uu____31682 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____31682 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____31732 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____31732, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____31767 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____31767 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____31854 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____31854 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____31941 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____31941
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
                              let uu____32021 = combine t11 t21 wl2  in
                              (match uu____32021 with
                               | (t12,ps,wl3) ->
                                   ((let uu____32102 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____32102
                                     then
                                       let uu____32107 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____32107
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____32189 ts1 =
               match uu____32189 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____32344 = pairwise out t wl2  in
                        (match uu____32344 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____32440 =
               let uu____32463 = FStar_List.hd ts  in (uu____32463, [], wl1)
                in
             let uu____32496 = FStar_List.tl ts  in
             aux uu____32440 uu____32496  in
           let uu____32511 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____32511 with
           | (this_flex,this_rigid) ->
               let uu____32601 =
                 let uu____32602 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____32602.FStar_Syntax_Syntax.n  in
               (match uu____32601 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____32653 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____32653
                    then
                      let uu____32656 = destruct_flex_t this_flex wl  in
                      (match uu____32656 with
                       | (flex,wl1) ->
                           let uu____32687 = quasi_pattern env flex  in
                           (match uu____32687 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____32726 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____32726
                                  then
                                    let uu____32731 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____32731
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____32746 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1929_32765 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1929_32765.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1929_32765.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1929_32765.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1929_32765.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1929_32765.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1929_32765.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1929_32765.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1929_32765.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1929_32765.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____32746)
                | uu____32806 ->
                    ((let uu____32808 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____32808
                      then
                        let uu____32813 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____32813
                      else ());
                     (let uu____32822 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____32822 with
                      | (u,_args) ->
                          let uu____32889 =
                            let uu____32890 = FStar_Syntax_Subst.compress u
                               in
                            uu____32890.FStar_Syntax_Syntax.n  in
                          (match uu____32889 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____32950 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____32950 with
                                 | (u',uu____32977) ->
                                     let uu____33018 =
                                       let uu____33019 = whnf env u'  in
                                       uu____33019.FStar_Syntax_Syntax.n  in
                                     (match uu____33018 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____33065 -> false)
                                  in
                               let uu____33067 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_33090  ->
                                         match uu___26_33090 with
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
                                              | uu____33150 -> false)
                                         | uu____33154 -> false))
                                  in
                               (match uu____33067 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____33173 = whnf env this_rigid
                                         in
                                      let uu____33182 =
                                        FStar_List.collect
                                          (fun uu___27_33196  ->
                                             match uu___27_33196 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____33221 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____33221]
                                             | uu____33261 -> [])
                                          bounds_probs
                                         in
                                      uu____33173 :: uu____33182  in
                                    let uu____33270 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____33270 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____33351 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____33417 =
                                               let uu____33418 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____33418.FStar_Syntax_Syntax.n
                                                in
                                             match uu____33417 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____33464 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____33464)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____33491 -> bound  in
                                           let uu____33492 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____33492)  in
                                         (match uu____33351 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____33667 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____33667
                                                then
                                                  let wl'1 =
                                                    let uu___1989_33689 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1989_33689.wl_deferred);
                                                      ctr =
                                                        (uu___1989_33689.ctr);
                                                      defer_ok =
                                                        (uu___1989_33689.defer_ok);
                                                      smt_ok =
                                                        (uu___1989_33689.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1989_33689.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1989_33689.tcenv);
                                                      wl_implicits =
                                                        (uu___1989_33689.wl_implicits)
                                                    }  in
                                                  let uu____33706 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____33706
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____33712 =
                                                  solve_t env eq_prob
                                                    (let uu___1994_33714 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___1994_33714.wl_deferred);
                                                       ctr =
                                                         (uu___1994_33714.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___1994_33714.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___1994_33714.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___1994_33714.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____33712 with
                                                | Success (uu____33736,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2000_33755 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2000_33755.wl_deferred);
                                                        ctr =
                                                          (uu___2000_33755.ctr);
                                                        defer_ok =
                                                          (uu___2000_33755.defer_ok);
                                                        smt_ok =
                                                          (uu___2000_33755.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2000_33755.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2000_33755.tcenv);
                                                        wl_implicits =
                                                          (uu___2000_33755.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2003_33789 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2003_33789.attempting);
                                                        wl_deferred =
                                                          (uu___2003_33789.wl_deferred);
                                                        ctr =
                                                          (uu___2003_33789.ctr);
                                                        defer_ok =
                                                          (uu___2003_33789.defer_ok);
                                                        smt_ok =
                                                          (uu___2003_33789.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2003_33789.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2003_33789.tcenv);
                                                        wl_implicits =
                                                          (FStar_List.append
                                                             wl'.wl_implicits
                                                             imps)
                                                      }  in
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
                                                    let uu____33865 =
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
                                                    ((let uu____33915 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____33915
                                                      then
                                                        let uu____33920 =
                                                          let uu____33922 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____33922
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____33920
                                                      else ());
                                                     (let uu____33935 =
                                                        let uu____33963 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____33963)
                                                         in
                                                      match uu____33935 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____34011))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____34085 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____34085
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
                                                                  let uu____34207
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____34207))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____34305 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____34305
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
                                                                    let uu____34435
                                                                    =
                                                                    let uu____34444
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____34444
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____34435
                                                                    [] wl2
                                                                     in
                                                                  let uu____34462
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____34462))))
                                                      | uu____34479 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____34508 when flip ->
                               let uu____34509 =
                                 let uu____34511 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____34513 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____34511 uu____34513
                                  in
                               failwith uu____34509
                           | uu____34516 ->
                               let uu____34517 =
                                 let uu____34519 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____34521 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____34519 uu____34521
                                  in
                               failwith uu____34517)))))

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
                      (fun uu____34640  ->
                         match uu____34640 with
                         | (x,i) ->
                             let uu____34678 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____34678, i)) bs_lhs
                     in
                  let uu____34693 = lhs  in
                  match uu____34693 with
                  | (uu____34694,u_lhs,uu____34696) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____34915 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____34933 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____34933, univ)
                             in
                          match uu____34915 with
                          | (k,univ) ->
                              let uu____34972 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____34972 with
                               | (uu____35026,u,wl3) ->
                                   let uu____35069 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____35069, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____35148 =
                              let uu____35173 =
                                let uu____35188 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____35188 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____35263  ->
                                   fun uu____35264  ->
                                     match (uu____35263, uu____35264) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____35457 =
                                           let uu____35484 =
                                             let uu____35495 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____35495
                                              in
                                           copy_uvar u_lhs [] uu____35484 wl2
                                            in
                                         (match uu____35457 with
                                          | (uu____35557,t_a,wl3) ->
                                              let uu____35600 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____35600 with
                                               | (uu____35651,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____35173
                                ([], wl1)
                               in
                            (match uu____35148 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2113_35829 = ct  in
                                   let uu____35840 =
                                     let uu____35851 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____35851
                                      in
                                   let uu____35878 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2113_35829.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2113_35829.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____35840;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____35878;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2113_35829.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2116_35916 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2116_35916.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2116_35916.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____35927 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____35927 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____36037 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____36037 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____36092 =
                                          let uu____36109 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____36109)  in
                                        TERM uu____36092  in
                                      let uu____36137 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____36137 with
                                       | (sub_prob,wl3) ->
                                           let uu____36185 =
                                             let uu____36202 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____36202
                                              in
                                           solve env uu____36185))
                             | (x,imp)::formals2 ->
                                 let uu____36264 =
                                   let uu____36291 =
                                     let uu____36302 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____36302
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____36291 wl1
                                    in
                                 (match uu____36264 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____36394 =
                                          let uu____36397 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____36397
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____36394 u_x
                                         in
                                      let uu____36398 =
                                        let uu____36401 =
                                          let uu____36404 =
                                            let uu____36405 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____36405, imp)  in
                                          [uu____36404]  in
                                        FStar_List.append bs_terms
                                          uu____36401
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____36398 formals2 wl2)
                              in
                           let uu____36464 = occurs_check u_lhs arrow1  in
                           (match uu____36464 with
                            | (uu____36485,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____36517 =
                                    let uu____36519 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____36519
                                     in
                                  giveup_or_defer env orig wl uu____36517
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
              (let uu____36689 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____36689
               then
                 let uu____36694 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____36697 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____36694 (rel_to_string (p_rel orig)) uu____36697
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____37012 = rhs wl1 scope env1 subst1  in
                     (match uu____37012 with
                      | (rhs_prob,wl2) ->
                          ((let uu____37069 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____37069
                            then
                              let uu____37074 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____37074
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____37230 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____37230 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2185_37242 = hd1  in
                       let uu____37253 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2185_37242.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2185_37242.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____37253
                       }  in
                     let hd21 =
                       let uu___2188_37275 = hd2  in
                       let uu____37286 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2188_37275.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2188_37275.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____37286
                       }  in
                     let uu____37297 =
                       let uu____37310 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____37310
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____37297 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____37374 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____37374
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____37494 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____37494 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____37645 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____37645
                                  in
                               ((let uu____37686 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____37686
                                 then
                                   let uu____37691 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____37693 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____37691
                                     uu____37693
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____37758 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____37820 = aux wl [] env [] bs1 bs2  in
               match uu____37820 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____37968 = attempt sub_probs wl2  in
                   solve env uu____37968)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist ->
             (FStar_TypeChecker_Common.prob * Prims.string) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2223_38207 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2223_38207.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2223_38207.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____38240 = try_solve env wl'  in
          match uu____38240 with
          | Success (uu____38241,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2232_38261 = wl  in
                  {
                    attempting = (uu___2232_38261.attempting);
                    wl_deferred = (uu___2232_38261.wl_deferred);
                    ctr = (uu___2232_38261.ctr);
                    defer_ok = (uu___2232_38261.defer_ok);
                    smt_ok = (uu___2232_38261.smt_ok);
                    umax_heuristic_ok = (uu___2232_38261.umax_heuristic_ok);
                    tcenv = (uu___2232_38261.tcenv);
                    wl_implicits = (FStar_List.append wl.wl_implicits imps)
                  }  in
                solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____38355 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____38355 wl)

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
            let binders_as_bv_set bs =
              let uu____38440 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____38440 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____38615 = lhs1  in
              match uu____38615 with
              | (uu____38618,ctx_u,uu____38620) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____38669 ->
                        let uu____38670 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____38670 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____38879 = quasi_pattern env1 lhs1  in
              match uu____38879 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____38937) ->
                  let uu____38954 = lhs1  in
                  (match uu____38954 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____39001 = occurs_check ctx_u rhs1  in
                       (match uu____39001 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____39092 =
                                let uu____39100 =
                                  let uu____39102 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____39102
                                   in
                                FStar_Util.Inl uu____39100  in
                              (uu____39092, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____39153 =
                                 let uu____39155 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____39155  in
                               if uu____39153
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____39203 =
                                    let uu____39211 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____39211  in
                                  let uu____39217 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____39203, uu____39217)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____39425 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____39425 with
              | (rhs_hd,args) ->
                  let uu____39492 = FStar_Util.prefix args  in
                  (match uu____39492 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____39600 = lhs1  in
                       (match uu____39600 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____39628 =
                              let uu____39655 =
                                let uu____39682 =
                                  let uu____39693 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____39693
                                   in
                                copy_uvar u_lhs [] uu____39682 wl1  in
                              match uu____39655 with
                              | (uu____39757,t_last_arg,wl2) ->
                                  let uu____39800 =
                                    let uu____39827 =
                                      let uu____39828 =
                                        let uu____39842 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____39842]  in
                                      FStar_List.append bs_lhs uu____39828
                                       in
                                    copy_uvar u_lhs uu____39827 t_res_lhs wl2
                                     in
                                  (match uu____39800 with
                                   | (uu____39913,lhs',wl3) ->
                                       let uu____39956 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____39956 with
                                        | (uu____40009,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____39628 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____40118 =
                                     let uu____40119 =
                                       let uu____40136 =
                                         let uu____40145 =
                                           let uu____40156 =
                                             let uu____40161 =
                                               let uu____40162 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____40162]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____40161
                                              in
                                           uu____40156
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____40145
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____40136)  in
                                     TERM uu____40119  in
                                   [uu____40118]  in
                                 let uu____40218 =
                                   let uu____40233 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____40233 with
                                   | (p1,wl3) ->
                                       let uu____40295 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____40295 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____40218 with
                                  | (sub_probs,wl3) ->
                                      let uu____40397 =
                                        let uu____40414 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____40414  in
                                      solve env1 uu____40397))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____40608 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____40608 with
                | (uu____40634,args) ->
                    (match args with | [] -> false | uu____40690 -> true)
                 in
              let is_arrow rhs2 =
                let uu____40721 =
                  let uu____40722 = FStar_Syntax_Subst.compress rhs2  in
                  uu____40722.FStar_Syntax_Syntax.n  in
                match uu____40721 with
                | FStar_Syntax_Syntax.Tm_arrow uu____40734 -> true
                | uu____40759 -> false  in
              let uu____40761 = quasi_pattern env1 lhs1  in
              match uu____40761 with
              | FStar_Pervasives_Native.None  ->
                  let uu____40780 =
                    let uu____40782 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____40782
                     in
                  giveup_or_defer env1 orig1 wl1 uu____40780
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____40803 = is_app rhs1  in
                  if uu____40803
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____40808 = is_arrow rhs1  in
                     if uu____40808
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____40813 =
                          let uu____40815 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____40815
                           in
                        giveup_or_defer env1 orig1 wl1 uu____40813))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____40826 = lhs  in
                (match uu____40826 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____40854 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____40854 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____40890 =
                              let uu____40894 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____40894
                               in
                            FStar_All.pipe_right uu____40890
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____40945 = occurs_check ctx_uv rhs1  in
                          (match uu____40945 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____40998 =
                                   let uu____41000 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____41000
                                    in
                                 giveup_or_defer env orig wl uu____40998
                               else
                                 (let uu____41006 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____41006
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____41034 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____41034
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____41058 =
                                         let uu____41060 =
                                           names_to_string1 fvs2  in
                                         let uu____41062 =
                                           names_to_string1 fvs1  in
                                         let uu____41064 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____41060 uu____41062
                                           uu____41064
                                          in
                                       giveup_or_defer env orig wl
                                         uu____41058)
                                    else first_order orig env wl lhs rhs1))
                      | uu____41081 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____41088 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____41088 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____41138 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____41138
                             | (FStar_Util.Inl msg,uu____41160) ->
                                 first_order orig env wl lhs rhs)))

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
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then giveup_or_defer env orig wl "flex-flex non-pattern"
                else
                  (let uu____41315 =
                     let uu____41340 = quasi_pattern env lhs  in
                     let uu____41351 = quasi_pattern env rhs  in
                     (uu____41340, uu____41351)  in
                   match uu____41315 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____41438 = lhs  in
                       (match uu____41438 with
                        | ({ FStar_Syntax_Syntax.n = uu____41439;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____41441;_},u_lhs,uu____41443)
                            ->
                            let uu____41470 = rhs  in
                            (match uu____41470 with
                             | (uu____41471,u_rhs,uu____41473) ->
                                 let uu____41498 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____41498
                                 then
                                   let uu____41505 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____41505
                                 else
                                   (let uu____41528 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____41528 with
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
                                        let uu____41570 =
                                          let uu____41597 =
                                            let uu____41608 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____41608
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____41597
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____41570 with
                                         | (uu____41632,w,wl1) ->
                                             let w_app =
                                               let uu____41686 =
                                                 let uu____41691 =
                                                   FStar_List.map
                                                     (fun uu____41707  ->
                                                        match uu____41707
                                                        with
                                                        | (z,uu____41720) ->
                                                            let uu____41735 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____41735) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____41691
                                                  in
                                               uu____41686
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____41745 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____41745
                                               then
                                                 let uu____41750 =
                                                   let uu____41754 =
                                                     flex_t_to_string lhs  in
                                                   let uu____41760 =
                                                     let uu____41764 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____41770 =
                                                       let uu____41774 =
                                                         term_to_string w  in
                                                       let uu____41776 =
                                                         let uu____41780 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____41794 =
                                                           let uu____41798 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____41812 =
                                                             let uu____41816
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____41816]
                                                              in
                                                           uu____41798 ::
                                                             uu____41812
                                                            in
                                                         uu____41780 ::
                                                           uu____41794
                                                          in
                                                       uu____41774 ::
                                                         uu____41776
                                                        in
                                                     uu____41764 ::
                                                       uu____41770
                                                      in
                                                   uu____41754 :: uu____41760
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____41750
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____41833 =
                                                     let uu____41850 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____41850)  in
                                                   TERM uu____41833  in
                                                 let uu____41878 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____41878
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____41886 =
                                                        let uu____41903 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____41903)
                                                         in
                                                      TERM uu____41886  in
                                                    [s1; s2])
                                                  in
                                               let uu____41931 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____41931))))))
                   | uu____41952 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____42233 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____42233
            then
              let uu____42238 = FStar_Syntax_Print.term_to_string t1  in
              let uu____42240 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____42242 = FStar_Syntax_Print.term_to_string t2  in
              let uu____42244 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____42238 uu____42240 uu____42242 uu____42244
            else ());
           (let uu____42255 = FStar_Syntax_Util.head_and_args t1  in
            match uu____42255 with
            | (head1,args1) ->
                let uu____42322 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____42322 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____42448 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____42448 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____42498 =
                         let uu____42500 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____42502 = args_to_string args1  in
                         let uu____42506 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____42508 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____42500 uu____42502 uu____42506 uu____42508
                          in
                       giveup env1 uu____42498 orig
                     else
                       (let uu____42515 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____42520 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____42520 = FStar_Syntax_Util.Equal)
                           in
                        if uu____42515
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2481_42524 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2481_42524.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2481_42524.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2481_42524.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2481_42524.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2481_42524.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2481_42524.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2481_42524.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2481_42524.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____42578 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____42578
                                    else solve env1 wl2))
                        else
                          (let uu____42603 = base_and_refinement env1 t1  in
                           match uu____42603 with
                           | (base1,refinement1) ->
                               let uu____42667 = base_and_refinement env1 t2
                                  in
                               (match uu____42667 with
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
                                           let uu____42997 =
                                             FStar_List.fold_right
                                               (fun uu____43061  ->
                                                  fun uu____43062  ->
                                                    match (uu____43061,
                                                            uu____43062)
                                                    with
                                                    | (((a1,uu____43154),
                                                        (a2,uu____43156)),
                                                       (probs,wl3)) ->
                                                        let uu____43261 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____43261
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____42997 with
                                           | (subprobs,wl3) ->
                                               ((let uu____43435 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____43435
                                                 then
                                                   let uu____43440 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____43440
                                                 else ());
                                                (let uu____43446 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____43446
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
                                                    (let uu____43613 =
                                                       mk_sub_probs wl3  in
                                                     match uu____43613 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____43661 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____43661
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____43697 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____43697))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____43869 =
                                                    mk_sub_probs wl3  in
                                                  match uu____43869 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____43927 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____43927)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____44031 =
                                           match uu____44031 with
                                           | (prob,reason) ->
                                               ((let uu____44104 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____44104
                                                 then
                                                   let uu____44109 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____44111 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____44109 uu____44111
                                                     reason
                                                 else ());
                                                (let uu____44116 =
                                                   let uu____44133 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____44140 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____44133, uu____44140)
                                                    in
                                                 match uu____44116 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____44189 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____44189 with
                                                      | (head1',uu____44215)
                                                          ->
                                                          let uu____44256 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____44256
                                                           with
                                                           | (head2',uu____44282)
                                                               ->
                                                               let uu____44323
                                                                 =
                                                                 let uu____44328
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____44329
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____44328,
                                                                   uu____44329)
                                                                  in
                                                               (match uu____44323
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____44331
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____44331
                                                                    then
                                                                    let uu____44336
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____44338
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____44340
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____44342
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____44336
                                                                    uu____44338
                                                                    uu____44340
                                                                    uu____44342
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____44347
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2567_44370
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2567_44370.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____44408
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____44408
                                                                    then
                                                                    let uu____44413
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____44413
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____44418 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____44438 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____44438 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____44446 =
                                             let uu____44447 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____44447.FStar_Syntax_Syntax.n
                                              in
                                           match uu____44446 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____44463 -> false  in
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
                                          | uu____44466 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____44469 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2587_44565 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2587_44565.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2587_44565.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2587_44565.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2587_44565.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2587_44565.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2587_44565.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2587_44565.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2587_44565.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____44857 = destruct_flex_t scrutinee wl1  in
             match uu____44857 with
             | ((_t,uv,_args),wl2) ->
                 let uu____44924 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____44924 with
                  | (xs,pat_term,uu____44961,uu____44962) ->
                      let uu____44993 =
                        FStar_List.fold_left
                          (fun uu____45037  ->
                             fun x  ->
                               match uu____45037 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____45103 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____45103 with
                                    | (uu____45155,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____44993 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____45273 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____45273 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2627_45392 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2627_45392.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2627_45392.umax_heuristic_ok);
                                    tcenv = (uu___2627_45392.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____45424 = solve env1 wl'  in
                                (match uu____45424 with
                                 | Success (uu____45435,imps) ->
                                     let wl'1 =
                                       let uu___2635_45454 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2635_45454.wl_deferred);
                                         ctr = (uu___2635_45454.ctr);
                                         defer_ok =
                                           (uu___2635_45454.defer_ok);
                                         smt_ok = (uu___2635_45454.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2635_45454.umax_heuristic_ok);
                                         tcenv = (uu___2635_45454.tcenv);
                                         wl_implicits =
                                           (uu___2635_45454.wl_implicits)
                                       }  in
                                     let uu____45471 = solve env1 wl'1  in
                                     (match uu____45471 with
                                      | Success (uu____45482,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2643_45494 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2643_45494.attempting);
                                                 wl_deferred =
                                                   (uu___2643_45494.wl_deferred);
                                                 ctr = (uu___2643_45494.ctr);
                                                 defer_ok =
                                                   (uu___2643_45494.defer_ok);
                                                 smt_ok =
                                                   (uu___2643_45494.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2643_45494.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2643_45494.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____45519 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____45534 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____45621 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____45621
                 then
                   let uu____45626 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____45628 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____45626 uu____45628
                 else ());
                (let uu____45633 =
                   let uu____45670 =
                     let uu____45687 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____45687)  in
                   let uu____45710 =
                     let uu____45727 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____45727)  in
                   (uu____45670, uu____45710)  in
                 match uu____45633 with
                 | ((uu____45797,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____45800;
                                   FStar_Syntax_Syntax.vars = uu____45801;_}),
                    (s,t)) ->
                     let uu____45950 =
                       let uu____45952 = is_flex scrutinee  in
                       Prims.op_Negation uu____45952  in
                     if uu____45950
                     then
                       ((let uu____45971 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____45971
                         then
                           let uu____45976 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____45976
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____46019 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____46019
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____46042 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____46042
                           then
                             let uu____46047 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____46049 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____46047 uu____46049
                           else ());
                          (let pat_discriminates uu___28_46085 =
                             match uu___28_46085 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____46109;
                                  FStar_Syntax_Syntax.p = uu____46110;_},FStar_Pervasives_Native.None
                                ,uu____46111) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____46144;
                                  FStar_Syntax_Syntax.p = uu____46145;_},FStar_Pervasives_Native.None
                                ,uu____46146) -> true
                             | uu____46198 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____46364 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____46364 with
                                       | (uu____46366,uu____46367,t') ->
                                           let uu____46407 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____46407 with
                                            | (FullMatch ,uu____46427) ->
                                                true
                                            | (HeadMatch
                                               uu____46457,uu____46458) ->
                                                true
                                            | uu____46489 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____46553 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____46553
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____46564 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____46564 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____46704,uu____46705) ->
                                       branches1
                                   | uu____46949 -> branches  in
                                 let uu____47037 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____47062 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____47062 with
                                        | (p,uu____47074,uu____47075) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _47150  -> FStar_Util.Inr _47150)
                                   uu____47037))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____47202 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____47202 with
                                | (p,uu____47219,e) ->
                                    ((let uu____47260 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____47260
                                      then
                                        let uu____47265 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____47267 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____47265 uu____47267
                                      else ());
                                     (let uu____47272 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _47319  -> FStar_Util.Inr _47319)
                                        uu____47272)))))
                 | ((s,t),(uu____47322,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____47325;
                                         FStar_Syntax_Syntax.vars =
                                           uu____47326;_}))
                     ->
                     let uu____47473 =
                       let uu____47475 = is_flex scrutinee  in
                       Prims.op_Negation uu____47475  in
                     if uu____47473
                     then
                       ((let uu____47494 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____47494
                         then
                           let uu____47499 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____47499
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____47542 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____47542
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____47565 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____47565
                           then
                             let uu____47570 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____47572 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____47570 uu____47572
                           else ());
                          (let pat_discriminates uu___28_47608 =
                             match uu___28_47608 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____47632;
                                  FStar_Syntax_Syntax.p = uu____47633;_},FStar_Pervasives_Native.None
                                ,uu____47634) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____47667;
                                  FStar_Syntax_Syntax.p = uu____47668;_},FStar_Pervasives_Native.None
                                ,uu____47669) -> true
                             | uu____47721 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____47887 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____47887 with
                                       | (uu____47889,uu____47890,t') ->
                                           let uu____47930 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____47930 with
                                            | (FullMatch ,uu____47950) ->
                                                true
                                            | (HeadMatch
                                               uu____47980,uu____47981) ->
                                                true
                                            | uu____48012 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____48076 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____48076
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____48087 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____48087 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____48227,uu____48228) ->
                                       branches1
                                   | uu____48472 -> branches  in
                                 let uu____48560 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____48585 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____48585 with
                                        | (p,uu____48597,uu____48598) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _48673  -> FStar_Util.Inr _48673)
                                   uu____48560))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____48725 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____48725 with
                                | (p,uu____48742,e) ->
                                    ((let uu____48783 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____48783
                                      then
                                        let uu____48788 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____48790 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____48788 uu____48790
                                      else ());
                                     (let uu____48795 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _48842  -> FStar_Util.Inr _48842)
                                        uu____48795)))))
                 | uu____48843 ->
                     ((let uu____48881 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____48881
                       then
                         let uu____48886 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____48888 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____48886 uu____48888
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____49106 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____49106
            then
              let uu____49111 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____49113 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____49115 = FStar_Syntax_Print.term_to_string t1  in
              let uu____49117 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____49111 uu____49113 uu____49115 uu____49117
            else ());
           (let uu____49122 = head_matches_delta env1 wl1 t1 t2  in
            match uu____49122 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____49185,uu____49186) ->
                     let rec may_relate head3 =
                       let uu____49238 =
                         let uu____49239 = FStar_Syntax_Subst.compress head3
                            in
                         uu____49239.FStar_Syntax_Syntax.n  in
                       match uu____49238 with
                       | FStar_Syntax_Syntax.Tm_name uu____49251 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____49258 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____49301 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____49301 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____49303 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____49306
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____49311 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____49314,uu____49315) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____49397) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____49411) ->
                           may_relate t
                       | uu____49424 -> false  in
                     let uu____49426 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____49426 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____49503 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____49503
                          then
                            let uu____49506 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____49506 with
                             | (guard,wl2) ->
                                 let uu____49549 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____49549)
                          else
                            (let uu____49572 =
                               let uu____49574 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____49576 =
                                 let uu____49578 =
                                   let uu____49582 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____49582
                                     (fun x  ->
                                        let uu____49589 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____49589)
                                    in
                                 FStar_Util.dflt "" uu____49578  in
                               let uu____49594 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____49596 =
                                 let uu____49598 =
                                   let uu____49602 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____49602
                                     (fun x  ->
                                        let uu____49609 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____49609)
                                    in
                                 FStar_Util.dflt "" uu____49598  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____49574 uu____49576 uu____49594
                                 uu____49596
                                in
                             giveup env1 uu____49572 orig))
                 | (HeadMatch (true ),uu____49615) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____49650 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____49650 with
                        | (guard,wl2) ->
                            let uu____49693 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____49693)
                     else
                       (let uu____49716 =
                          let uu____49718 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____49720 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____49718 uu____49720
                           in
                        giveup env1 uu____49716 orig)
                 | (uu____49723,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2816_49769 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2816_49769.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2816_49769.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2816_49769.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2816_49769.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2816_49769.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2816_49769.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2816_49769.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2816_49769.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____49864 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____49864
          then
            let uu____49879 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____49879
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____49929 =
                let uu____49937 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____49937  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____49929 t1);
             (let uu____49976 =
                let uu____49984 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____49984  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____49976 t2);
             (let uu____50023 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____50023
              then
                let uu____50027 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____50033 =
                  let uu____50035 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____50037 =
                    let uu____50039 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____50039  in
                  Prims.op_Hat uu____50035 uu____50037  in
                let uu____50042 =
                  let uu____50044 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____50046 =
                    let uu____50048 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____50048  in
                  Prims.op_Hat uu____50044 uu____50046  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____50027 uu____50033 uu____50042
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____50059,uu____50060) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____50092,FStar_Syntax_Syntax.Tm_delayed uu____50093) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____50125,uu____50126) ->
                  let uu____50173 =
                    let uu___2847_50174 = problem  in
                    let uu____50175 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2847_50174.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____50175;
                      FStar_TypeChecker_Common.relation =
                        (uu___2847_50174.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2847_50174.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2847_50174.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2847_50174.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2847_50174.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2847_50174.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2847_50174.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2847_50174.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____50173 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____50224,uu____50225) ->
                  let uu____50236 =
                    let uu___2853_50237 = problem  in
                    let uu____50238 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2853_50237.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____50238;
                      FStar_TypeChecker_Common.relation =
                        (uu___2853_50237.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2853_50237.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2853_50237.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2853_50237.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2853_50237.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2853_50237.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2853_50237.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2853_50237.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____50236 wl
              | (uu____50287,FStar_Syntax_Syntax.Tm_ascribed uu____50288) ->
                  let uu____50335 =
                    let uu___2859_50336 = problem  in
                    let uu____50337 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2859_50336.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2859_50336.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2859_50336.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____50337;
                      FStar_TypeChecker_Common.element =
                        (uu___2859_50336.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2859_50336.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2859_50336.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2859_50336.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2859_50336.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2859_50336.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____50335 wl
              | (uu____50386,FStar_Syntax_Syntax.Tm_meta uu____50387) ->
                  let uu____50398 =
                    let uu___2865_50399 = problem  in
                    let uu____50400 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2865_50399.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2865_50399.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2865_50399.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____50400;
                      FStar_TypeChecker_Common.element =
                        (uu___2865_50399.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2865_50399.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2865_50399.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2865_50399.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2865_50399.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2865_50399.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____50398 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____50450),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____50452)) ->
                  let uu____50485 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____50485
              | (FStar_Syntax_Syntax.Tm_bvar uu____50506,uu____50507) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____50514,FStar_Syntax_Syntax.Tm_bvar uu____50515) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_50639 =
                    match uu___29_50639 with
                    | [] -> c
                    | bs ->
                        let uu____50690 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____50690
                     in
                  let uu____50718 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____50718 with
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
                                    let uu____51054 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____51054
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
                  let mk_t t l uu___30_51236 =
                    match uu___30_51236 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____51324 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____51324 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____51640 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____51649 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____51640
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____51649 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____51668,uu____51669) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____51724 -> true
                    | uu____51760 -> false  in
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
                      (let uu____51900 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2967_51920 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2967_51920.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2967_51920.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2967_51920.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2967_51920.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2967_51920.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2967_51920.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2967_51920.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2967_51920.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2967_51920.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2967_51920.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2967_51920.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2967_51920.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2967_51920.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2967_51920.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2967_51920.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2967_51920.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2967_51920.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2967_51920.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2967_51920.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2967_51920.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2967_51920.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2967_51920.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2967_51920.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2967_51920.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2967_51920.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2967_51920.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2967_51920.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2967_51920.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2967_51920.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2967_51920.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2967_51920.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2967_51920.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2967_51920.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2967_51920.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2967_51920.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2967_51920.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2967_51920.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2967_51920.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2967_51920.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2967_51920.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____51900 with
                       | (uu____52041,ty,uu____52043) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____52104 =
                                 let uu____52105 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____52105.FStar_Syntax_Syntax.n  in
                               match uu____52104 with
                               | FStar_Syntax_Syntax.Tm_refine uu____52120 ->
                                   let uu____52136 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____52136
                               | uu____52145 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____52156 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____52156
                             then
                               let uu____52161 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____52163 =
                                 let uu____52165 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____52165
                                  in
                               let uu____52174 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____52161 uu____52163 uu____52174
                             else ());
                            r1))
                     in
                  let uu____52179 =
                    let uu____52212 = maybe_eta t1  in
                    let uu____52227 = maybe_eta t2  in
                    (uu____52212, uu____52227)  in
                  (match uu____52179 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2988_52333 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2988_52333.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2988_52333.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2988_52333.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2988_52333.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2988_52333.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2988_52333.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2988_52333.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2988_52333.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____52430 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____52430
                       then
                         let uu____52433 = destruct_flex_t not_abs wl  in
                         (match uu____52433 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_52490 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_52490.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_52490.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_52490.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_52490.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_52490.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_52490.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_52490.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_52490.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____52590 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____52590
                       then
                         let uu____52593 = destruct_flex_t not_abs wl  in
                         (match uu____52593 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_52650 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_52650.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_52650.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_52650.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_52650.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_52650.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_52650.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_52650.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_52650.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____52690 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____52724,FStar_Syntax_Syntax.Tm_abs uu____52725) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____52780 -> true
                    | uu____52816 -> false  in
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
                      (let uu____52956 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2967_52976 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2967_52976.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2967_52976.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2967_52976.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2967_52976.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2967_52976.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2967_52976.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2967_52976.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2967_52976.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2967_52976.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___2967_52976.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2967_52976.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2967_52976.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2967_52976.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2967_52976.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2967_52976.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2967_52976.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2967_52976.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2967_52976.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2967_52976.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2967_52976.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2967_52976.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2967_52976.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2967_52976.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2967_52976.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2967_52976.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2967_52976.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2967_52976.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2967_52976.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2967_52976.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2967_52976.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2967_52976.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2967_52976.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2967_52976.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2967_52976.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2967_52976.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2967_52976.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2967_52976.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2967_52976.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2967_52976.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2967_52976.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____52956 with
                       | (uu____53097,ty,uu____53099) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____53160 =
                                 let uu____53161 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____53161.FStar_Syntax_Syntax.n  in
                               match uu____53160 with
                               | FStar_Syntax_Syntax.Tm_refine uu____53176 ->
                                   let uu____53192 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____53192
                               | uu____53201 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____53212 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____53212
                             then
                               let uu____53217 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____53219 =
                                 let uu____53221 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____53221
                                  in
                               let uu____53230 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____53217 uu____53219 uu____53230
                             else ());
                            r1))
                     in
                  let uu____53235 =
                    let uu____53268 = maybe_eta t1  in
                    let uu____53283 = maybe_eta t2  in
                    (uu____53268, uu____53283)  in
                  (match uu____53235 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___2988_53389 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___2988_53389.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___2988_53389.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___2988_53389.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___2988_53389.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___2988_53389.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___2988_53389.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___2988_53389.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___2988_53389.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____53486 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____53486
                       then
                         let uu____53489 = destruct_flex_t not_abs wl  in
                         (match uu____53489 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_53546 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_53546.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_53546.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_53546.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_53546.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_53546.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_53546.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_53546.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_53546.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____53646 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____53646
                       then
                         let uu____53649 = destruct_flex_t not_abs wl  in
                         (match uu____53649 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3005_53706 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3005_53706.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3005_53706.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3005_53706.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3005_53706.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3005_53706.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3005_53706.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3005_53706.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3005_53706.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____53746 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____53828 =
                    let uu____53843 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____53843 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3028_53931 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3028_53931.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3028_53931.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3030_53943 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3030_53943.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3030_53943.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____53954,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3028_54011 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3028_54011.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3028_54011.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3030_54023 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3030_54023.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3030_54023.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____54034 -> (x1, x2)  in
                  (match uu____53828 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____54107 = as_refinement false env t11  in
                       (match uu____54107 with
                        | (x12,phi11) ->
                            let uu____54142 = as_refinement false env t21  in
                            (match uu____54142 with
                             | (x22,phi21) ->
                                 ((let uu____54178 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____54178
                                   then
                                     ((let uu____54183 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____54185 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____54187 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____54183
                                         uu____54185 uu____54187);
                                      (let uu____54190 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____54192 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____54194 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____54190
                                         uu____54192 uu____54194))
                                   else ());
                                  (let uu____54199 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____54199 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            ((Prims.parse_int "0"), x13)]
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
                                         let uu____54490 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____54490
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____54522 =
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
                                         (let uu____54559 =
                                            let uu____54567 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____54567
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____54559
                                            (p_guard base_prob));
                                         (let uu____54606 =
                                            let uu____54614 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____54614
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____54606
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____54673 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____54673)
                                          in
                                       let has_uvars =
                                         (let uu____54694 =
                                            let uu____54696 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____54696
                                             in
                                          Prims.op_Negation uu____54694) ||
                                           (let uu____54716 =
                                              let uu____54718 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____54718
                                               in
                                            Prims.op_Negation uu____54716)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____54742 =
                                           let uu____54755 =
                                             let uu____54769 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____54769]  in
                                           mk_t_problem wl1 uu____54755 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____54742 with
                                          | (ref_prob,wl2) ->
                                              let uu____54827 =
                                                solve env1
                                                  (let uu___3072_54829 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3072_54829.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3072_54829.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3072_54829.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3072_54829.tcenv);
                                                     wl_implicits =
                                                       (uu___3072_54829.wl_implicits)
                                                   })
                                                 in
                                              (match uu____54827 with
                                               | Failed (prob,msg) ->
                                                   if
                                                     ((Prims.op_Negation
                                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                        && has_uvars)
                                                       ||
                                                       (Prims.op_Negation
                                                          wl2.smt_ok)
                                                   then giveup env1 msg prob
                                                   else fallback ()
                                               | Success uu____54862 ->
                                                   let guard =
                                                     let uu____54878 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____54878
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3083_54943 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3083_54943.attempting);
                                                       wl_deferred =
                                                         (uu___3083_54943.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3083_54943.defer_ok);
                                                       smt_ok =
                                                         (uu___3083_54943.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3083_54943.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3083_54943.tcenv);
                                                       wl_implicits =
                                                         (uu___3083_54943.wl_implicits)
                                                     }  in
                                                   let uu____54961 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____54961))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____54980,FStar_Syntax_Syntax.Tm_uvar uu____54981) ->
                  let uu____55022 = destruct_flex_t t1 wl  in
                  (match uu____55022 with
                   | (f1,wl1) ->
                       let uu____55053 = destruct_flex_t t2 wl1  in
                       (match uu____55053 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____55084;
                    FStar_Syntax_Syntax.pos = uu____55085;
                    FStar_Syntax_Syntax.vars = uu____55086;_},uu____55087),FStar_Syntax_Syntax.Tm_uvar
                 uu____55088) ->
                  let uu____55169 = destruct_flex_t t1 wl  in
                  (match uu____55169 with
                   | (f1,wl1) ->
                       let uu____55200 = destruct_flex_t t2 wl1  in
                       (match uu____55200 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____55231,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____55232;
                    FStar_Syntax_Syntax.pos = uu____55233;
                    FStar_Syntax_Syntax.vars = uu____55234;_},uu____55235))
                  ->
                  let uu____55316 = destruct_flex_t t1 wl  in
                  (match uu____55316 with
                   | (f1,wl1) ->
                       let uu____55347 = destruct_flex_t t2 wl1  in
                       (match uu____55347 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____55378;
                    FStar_Syntax_Syntax.pos = uu____55379;
                    FStar_Syntax_Syntax.vars = uu____55380;_},uu____55381),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____55382;
                    FStar_Syntax_Syntax.pos = uu____55383;
                    FStar_Syntax_Syntax.vars = uu____55384;_},uu____55385))
                  ->
                  let uu____55506 = destruct_flex_t t1 wl  in
                  (match uu____55506 with
                   | (f1,wl1) ->
                       let uu____55537 = destruct_flex_t t2 wl1  in
                       (match uu____55537 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____55568,uu____55569) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____55594 = destruct_flex_t t1 wl  in
                  (match uu____55594 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____55625;
                    FStar_Syntax_Syntax.pos = uu____55626;
                    FStar_Syntax_Syntax.vars = uu____55627;_},uu____55628),uu____55629)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____55694 = destruct_flex_t t1 wl  in
                  (match uu____55694 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____55725,FStar_Syntax_Syntax.Tm_uvar uu____55726) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____55755,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____55756;
                    FStar_Syntax_Syntax.pos = uu____55757;
                    FStar_Syntax_Syntax.vars = uu____55758;_},uu____55759))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____55828,FStar_Syntax_Syntax.Tm_arrow uu____55829) ->
                  solve_t' env
                    (let uu___3183_55874 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3183_55874.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3183_55874.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3183_55874.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3183_55874.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3183_55874.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3183_55874.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3183_55874.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3183_55874.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3183_55874.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____55915;
                    FStar_Syntax_Syntax.pos = uu____55916;
                    FStar_Syntax_Syntax.vars = uu____55917;_},uu____55918),FStar_Syntax_Syntax.Tm_arrow
                 uu____55919) ->
                  solve_t' env
                    (let uu___3183_56004 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3183_56004.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3183_56004.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3183_56004.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3183_56004.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3183_56004.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3183_56004.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3183_56004.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3183_56004.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3183_56004.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____56045,FStar_Syntax_Syntax.Tm_uvar uu____56046) ->
                  let uu____56067 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____56067
              | (uu____56084,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____56085;
                    FStar_Syntax_Syntax.pos = uu____56086;
                    FStar_Syntax_Syntax.vars = uu____56087;_},uu____56088))
                  ->
                  let uu____56149 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____56149
              | (FStar_Syntax_Syntax.Tm_uvar uu____56166,uu____56167) ->
                  let uu____56188 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____56188
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____56205;
                    FStar_Syntax_Syntax.pos = uu____56206;
                    FStar_Syntax_Syntax.vars = uu____56207;_},uu____56208),uu____56209)
                  ->
                  let uu____56270 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____56270
              | (FStar_Syntax_Syntax.Tm_refine uu____56287,uu____56288) ->
                  let t21 =
                    let uu____56313 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____56313  in
                  solve_t env
                    (let uu___3218_56369 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3218_56369.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3218_56369.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3218_56369.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3218_56369.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3218_56369.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3218_56369.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3218_56369.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3218_56369.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3218_56369.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____56410,FStar_Syntax_Syntax.Tm_refine uu____56411) ->
                  let t11 =
                    let uu____56436 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____56436  in
                  solve_t env
                    (let uu___3225_56492 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3225_56492.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3225_56492.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3225_56492.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3225_56492.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3225_56492.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3225_56492.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3225_56492.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3225_56492.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3225_56492.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____56674 =
                    let uu____56675 = guard_of_prob env wl problem t1 t2  in
                    match uu____56675 with
                    | (guard,wl1) ->
                        let uu____56718 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____56718
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____57119 = br1  in
                        (match uu____57119 with
                         | (p1,w1,uu____57167) ->
                             let uu____57206 = br2  in
                             (match uu____57206 with
                              | (p2,w2,uu____57245) ->
                                  let uu____57266 =
                                    let uu____57268 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____57268  in
                                  if uu____57266
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____57311 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____57311 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____57378 = br2  in
                                         (match uu____57378 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____57463 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____57463
                                                 in
                                              let uu____57483 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____57538,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____57587) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____57730 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____57730 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____57483
                                                (fun uu____57871  ->
                                                   match uu____57871 with
                                                   | (wprobs,wl2) ->
                                                       let uu____57940 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____57940
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____57998
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____57998
                                                              then
                                                                let uu____58003
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____58005
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____58003
                                                                  uu____58005
                                                              else ());
                                                             (let uu____58011
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____58011
                                                                (fun
                                                                   uu____58071
                                                                    ->
                                                                   match uu____58071
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
                    | uu____58302 -> FStar_Pervasives_Native.None  in
                  let uu____58370 = solve_branches wl brs1 brs2  in
                  (match uu____58370 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____58461 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____58461 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____58542 =
                                FStar_List.map
                                  (fun uu____58562  ->
                                     match uu____58562 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____58542  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____58595 =
                              let uu____58596 =
                                let uu____58613 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____58613
                                  (let uu___3324_58621 = wl3  in
                                   {
                                     attempting =
                                       (uu___3324_58621.attempting);
                                     wl_deferred =
                                       (uu___3324_58621.wl_deferred);
                                     ctr = (uu___3324_58621.ctr);
                                     defer_ok = (uu___3324_58621.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3324_58621.umax_heuristic_ok);
                                     tcenv = (uu___3324_58621.tcenv);
                                     wl_implicits =
                                       (uu___3324_58621.wl_implicits)
                                   })
                                 in
                              solve env uu____58596  in
                            (match uu____58595 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____58642 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____58649,uu____58650) ->
                  let head1 =
                    let uu____58697 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____58697
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____58779 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____58779
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____58853 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____58853
                    then
                      let uu____58857 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____58863 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____58865 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____58857 uu____58863 uu____58865
                    else ());
                   (let no_free_uvars t =
                      (let uu____58887 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____58887) &&
                        (let uu____58907 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____58907)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____58956 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____58956 = FStar_Syntax_Util.Equal  in
                    let uu____58957 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____58957
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____58965 = equal t1 t2  in
                         (if uu____58965
                          then
                            let uu____58968 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____58968
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____58993 =
                            let uu____59012 = equal t1 t2  in
                            if uu____59012
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____59053 = mk_eq2 wl env orig t1 t2  in
                               match uu____59053 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____58993 with
                          | (guard,wl1) ->
                              let uu____59162 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____59162))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____59181,uu____59182) ->
                  let head1 =
                    let uu____59202 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____59202
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____59284 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____59284
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____59358 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____59358
                    then
                      let uu____59362 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____59368 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____59370 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____59362 uu____59368 uu____59370
                    else ());
                   (let no_free_uvars t =
                      (let uu____59392 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____59392) &&
                        (let uu____59412 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____59412)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____59461 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____59461 = FStar_Syntax_Util.Equal  in
                    let uu____59462 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____59462
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____59470 = equal t1 t2  in
                         (if uu____59470
                          then
                            let uu____59473 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____59473
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____59498 =
                            let uu____59517 = equal t1 t2  in
                            if uu____59517
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____59558 = mk_eq2 wl env orig t1 t2  in
                               match uu____59558 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____59498 with
                          | (guard,wl1) ->
                              let uu____59667 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____59667))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____59686,uu____59687) ->
                  let head1 =
                    let uu____59702 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____59702
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____59784 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____59784
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____59858 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____59858
                    then
                      let uu____59862 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____59868 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____59870 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____59862 uu____59868 uu____59870
                    else ());
                   (let no_free_uvars t =
                      (let uu____59892 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____59892) &&
                        (let uu____59912 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____59912)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____59961 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____59961 = FStar_Syntax_Util.Equal  in
                    let uu____59962 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____59962
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____59970 = equal t1 t2  in
                         (if uu____59970
                          then
                            let uu____59973 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____59973
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____59998 =
                            let uu____60017 = equal t1 t2  in
                            if uu____60017
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____60058 = mk_eq2 wl env orig t1 t2  in
                               match uu____60058 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____59998 with
                          | (guard,wl1) ->
                              let uu____60167 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____60167))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____60186,uu____60187) ->
                  let head1 =
                    let uu____60197 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____60197
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____60279 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____60279
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____60353 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____60353
                    then
                      let uu____60357 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____60363 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____60365 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____60357 uu____60363 uu____60365
                    else ());
                   (let no_free_uvars t =
                      (let uu____60387 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____60387) &&
                        (let uu____60407 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____60407)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____60456 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____60456 = FStar_Syntax_Util.Equal  in
                    let uu____60457 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____60457
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____60465 = equal t1 t2  in
                         (if uu____60465
                          then
                            let uu____60468 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____60468
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____60493 =
                            let uu____60512 = equal t1 t2  in
                            if uu____60512
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____60553 = mk_eq2 wl env orig t1 t2  in
                               match uu____60553 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____60493 with
                          | (guard,wl1) ->
                              let uu____60662 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____60662))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____60681,uu____60682) ->
                  let head1 =
                    let uu____60695 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____60695
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____60777 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____60777
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____60851 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____60851
                    then
                      let uu____60855 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____60861 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____60863 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____60855 uu____60861 uu____60863
                    else ());
                   (let no_free_uvars t =
                      (let uu____60885 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____60885) &&
                        (let uu____60905 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____60905)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____60954 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____60954 = FStar_Syntax_Util.Equal  in
                    let uu____60955 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____60955
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____60963 = equal t1 t2  in
                         (if uu____60963
                          then
                            let uu____60966 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____60966
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____60991 =
                            let uu____61010 = equal t1 t2  in
                            if uu____61010
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____61051 = mk_eq2 wl env orig t1 t2  in
                               match uu____61051 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____60991 with
                          | (guard,wl1) ->
                              let uu____61160 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____61160))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____61179,uu____61180) ->
                  let head1 =
                    let uu____61214 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____61214
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____61296 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____61296
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____61370 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____61370
                    then
                      let uu____61374 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____61380 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____61382 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____61374 uu____61380 uu____61382
                    else ());
                   (let no_free_uvars t =
                      (let uu____61404 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____61404) &&
                        (let uu____61424 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____61424)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____61473 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____61473 = FStar_Syntax_Util.Equal  in
                    let uu____61474 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____61474
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____61482 = equal t1 t2  in
                         (if uu____61482
                          then
                            let uu____61485 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____61485
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____61510 =
                            let uu____61529 = equal t1 t2  in
                            if uu____61529
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____61570 = mk_eq2 wl env orig t1 t2  in
                               match uu____61570 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____61510 with
                          | (guard,wl1) ->
                              let uu____61679 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____61679))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____61698,FStar_Syntax_Syntax.Tm_match uu____61699) ->
                  let head1 =
                    let uu____61746 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____61746
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____61828 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____61828
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____61902 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____61902
                    then
                      let uu____61906 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____61912 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____61914 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____61906 uu____61912 uu____61914
                    else ());
                   (let no_free_uvars t =
                      (let uu____61936 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____61936) &&
                        (let uu____61956 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____61956)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____62005 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____62005 = FStar_Syntax_Util.Equal  in
                    let uu____62006 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____62006
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____62014 = equal t1 t2  in
                         (if uu____62014
                          then
                            let uu____62017 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____62017
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____62042 =
                            let uu____62061 = equal t1 t2  in
                            if uu____62061
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____62102 = mk_eq2 wl env orig t1 t2  in
                               match uu____62102 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____62042 with
                          | (guard,wl1) ->
                              let uu____62211 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____62211))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____62230,FStar_Syntax_Syntax.Tm_uinst uu____62231) ->
                  let head1 =
                    let uu____62251 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____62251
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____62327 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____62327
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____62395 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____62395
                    then
                      let uu____62399 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____62405 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____62407 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____62399 uu____62405 uu____62407
                    else ());
                   (let no_free_uvars t =
                      (let uu____62429 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____62429) &&
                        (let uu____62449 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____62449)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____62498 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____62498 = FStar_Syntax_Util.Equal  in
                    let uu____62499 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____62499
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____62507 = equal t1 t2  in
                         (if uu____62507
                          then
                            let uu____62510 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____62510
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____62535 =
                            let uu____62554 = equal t1 t2  in
                            if uu____62554
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____62595 = mk_eq2 wl env orig t1 t2  in
                               match uu____62595 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____62535 with
                          | (guard,wl1) ->
                              let uu____62704 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____62704))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____62723,FStar_Syntax_Syntax.Tm_name uu____62724) ->
                  let head1 =
                    let uu____62739 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____62739
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____62815 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____62815
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____62883 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____62883
                    then
                      let uu____62887 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____62893 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____62895 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____62887 uu____62893 uu____62895
                    else ());
                   (let no_free_uvars t =
                      (let uu____62917 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____62917) &&
                        (let uu____62937 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____62937)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____62986 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____62986 = FStar_Syntax_Util.Equal  in
                    let uu____62987 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____62987
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____62995 = equal t1 t2  in
                         (if uu____62995
                          then
                            let uu____62998 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____62998
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____63023 =
                            let uu____63042 = equal t1 t2  in
                            if uu____63042
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____63083 = mk_eq2 wl env orig t1 t2  in
                               match uu____63083 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____63023 with
                          | (guard,wl1) ->
                              let uu____63192 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____63192))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____63211,FStar_Syntax_Syntax.Tm_constant uu____63212) ->
                  let head1 =
                    let uu____63222 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____63222
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____63298 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____63298
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____63366 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____63366
                    then
                      let uu____63370 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____63376 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____63378 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____63370 uu____63376 uu____63378
                    else ());
                   (let no_free_uvars t =
                      (let uu____63400 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____63400) &&
                        (let uu____63420 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____63420)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____63469 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____63469 = FStar_Syntax_Util.Equal  in
                    let uu____63470 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____63470
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____63478 = equal t1 t2  in
                         (if uu____63478
                          then
                            let uu____63481 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____63481
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____63506 =
                            let uu____63525 = equal t1 t2  in
                            if uu____63525
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____63566 = mk_eq2 wl env orig t1 t2  in
                               match uu____63566 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____63506 with
                          | (guard,wl1) ->
                              let uu____63675 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____63675))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____63694,FStar_Syntax_Syntax.Tm_fvar uu____63695) ->
                  let head1 =
                    let uu____63708 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____63708
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____63784 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____63784
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____63852 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____63852
                    then
                      let uu____63856 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____63862 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____63864 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____63856 uu____63862 uu____63864
                    else ());
                   (let no_free_uvars t =
                      (let uu____63886 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____63886) &&
                        (let uu____63906 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____63906)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____63955 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____63955 = FStar_Syntax_Util.Equal  in
                    let uu____63956 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____63956
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____63964 = equal t1 t2  in
                         (if uu____63964
                          then
                            let uu____63967 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____63967
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____63992 =
                            let uu____64011 = equal t1 t2  in
                            if uu____64011
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____64052 = mk_eq2 wl env orig t1 t2  in
                               match uu____64052 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____63992 with
                          | (guard,wl1) ->
                              let uu____64161 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____64161))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____64180,FStar_Syntax_Syntax.Tm_app uu____64181) ->
                  let head1 =
                    let uu____64215 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____64215
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____64291 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____64291
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____64359 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____64359
                    then
                      let uu____64363 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____64369 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____64371 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____64363 uu____64369 uu____64371
                    else ());
                   (let no_free_uvars t =
                      (let uu____64393 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____64393) &&
                        (let uu____64413 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____64413)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____64462 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____64462 = FStar_Syntax_Util.Equal  in
                    let uu____64463 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____64463
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____64471 = equal t1 t2  in
                         (if uu____64471
                          then
                            let uu____64474 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____64474
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____64499 =
                            let uu____64518 = equal t1 t2  in
                            if uu____64518
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____64559 = mk_eq2 wl env orig t1 t2  in
                               match uu____64559 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____64499 with
                          | (guard,wl1) ->
                              let uu____64668 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____64668))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____64687,FStar_Syntax_Syntax.Tm_let uu____64688) ->
                  let uu____64737 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____64737
                  then
                    let uu____64740 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____64740
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____64764,uu____64765) ->
                  let uu____64790 =
                    let uu____64796 =
                      let uu____64798 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____64800 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____64802 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____64804 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____64798 uu____64800 uu____64802 uu____64804
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____64796)
                     in
                  FStar_Errors.raise_error uu____64790
                    t1.FStar_Syntax_Syntax.pos
              | (uu____64808,FStar_Syntax_Syntax.Tm_let uu____64809) ->
                  let uu____64834 =
                    let uu____64840 =
                      let uu____64842 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____64844 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____64846 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____64848 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____64842 uu____64844 uu____64846 uu____64848
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____64840)
                     in
                  FStar_Errors.raise_error uu____64834
                    t1.FStar_Syntax_Syntax.pos
              | uu____64852 -> giveup env "head tag mismatch" orig))))

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
        let solve_eq c1_comp c2_comp =
          (let uu____65076 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____65076
           then
             let uu____65081 =
               let uu____65083 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____65083  in
             let uu____65092 =
               let uu____65094 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____65094  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____65081 uu____65092
           else ());
          (let uu____65106 =
             let uu____65108 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____65108  in
           if uu____65106
           then
             let uu____65111 =
               let uu____65113 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____65115 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____65113 uu____65115
                in
             giveup env uu____65111 orig
           else
             (let uu____65120 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____65120 with
              | (ret_sub_prob,wl1) ->
                  let uu____65152 =
                    FStar_List.fold_right2
                      (fun uu____65213  ->
                         fun uu____65214  ->
                           fun uu____65215  ->
                             match (uu____65213, uu____65214, uu____65215)
                             with
                             | ((a1,uu____65299),(a2,uu____65301),(arg_sub_probs,wl2))
                                 ->
                                 let uu____65382 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____65382 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____65152 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____65484 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____65484  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____65520 = attempt sub_probs wl3  in
                       solve env uu____65520)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____65598 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____65613)::[] -> wp1
              | uu____65654 ->
                  let uu____65669 =
                    let uu____65671 =
                      let uu____65673 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____65673  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____65671
                     in
                  failwith uu____65669
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____65684 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____65684]
              | x -> x  in
            let uu____65686 =
              let uu____65701 =
                let uu____65714 =
                  let uu____65723 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____65723 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____65714  in
              [uu____65701]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____65686;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____65753 = lift_c1 ()  in solve_eq uu____65753 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___31_65772  ->
                       match uu___31_65772 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____65777 -> false))
                in
             let uu____65779 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____65833)::uu____65834,(wp2,uu____65836)::uu____65837)
                   -> (wp1, wp2)
               | uu____65958 ->
                   let uu____65991 =
                     let uu____65997 =
                       let uu____65999 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____66001 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____65999 uu____66001
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____65997)
                      in
                   FStar_Errors.raise_error uu____65991
                     env.FStar_TypeChecker_Env.range
                in
             match uu____65779 with
             | (wpc1,wpc2) ->
                 let uu____66035 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____66035
                 then
                   let uu____66044 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____66044 wl
                 else
                   (let uu____66057 =
                      let uu____66084 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____66084  in
                    match uu____66057 with
                    | (c2_decl,qualifiers) ->
                        let uu____66185 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____66185
                        then
                          let c1_repr =
                            let uu____66200 =
                              let uu____66209 =
                                let uu____66218 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____66218  in
                              let uu____66229 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____66209 uu____66229
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____66200
                             in
                          let c2_repr =
                            let uu____66239 =
                              let uu____66248 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____66257 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____66248 uu____66257
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____66239
                             in
                          let uu____66258 =
                            let uu____66271 =
                              let uu____66273 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____66275 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____66273 uu____66275
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____66271
                             in
                          (match uu____66258 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____66321 = attempt [prob] wl2  in
                               solve env uu____66321)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____66368 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____66368
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____66377 =
                                     let uu____66384 =
                                       let uu____66385 =
                                         let uu____66410 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____66421 =
                                           let uu____66436 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____66449 =
                                             let uu____66464 =
                                               let uu____66477 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____66477
                                                in
                                             [uu____66464]  in
                                           uu____66436 :: uu____66449  in
                                         (uu____66410, uu____66421)  in
                                       FStar_Syntax_Syntax.Tm_app uu____66385
                                        in
                                     FStar_Syntax_Syntax.mk uu____66384  in
                                   uu____66377 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____66562 =
                                    let uu____66569 =
                                      let uu____66570 =
                                        let uu____66595 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____66606 =
                                          let uu____66621 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____66634 =
                                            let uu____66649 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____66662 =
                                              let uu____66677 =
                                                let uu____66690 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____66690
                                                 in
                                              [uu____66677]  in
                                            uu____66649 :: uu____66662  in
                                          uu____66621 :: uu____66634  in
                                        (uu____66595, uu____66606)  in
                                      FStar_Syntax_Syntax.Tm_app uu____66570
                                       in
                                    FStar_Syntax_Syntax.mk uu____66569  in
                                  uu____66562 FStar_Pervasives_Native.None r)
                              in
                           (let uu____66784 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____66784
                            then
                              let uu____66789 =
                                let uu____66791 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding
                                      true;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____66791
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____66789
                            else ());
                           (let uu____66804 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____66804 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____66857 =
                                    let uu____66864 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _66887  ->
                                         FStar_Pervasives_Native.Some _66887)
                                      uu____66864
                                     in
                                  solve_prob orig uu____66857 [] wl1  in
                                let uu____66888 = attempt [base_prob] wl2  in
                                solve env uu____66888))))
           in
        let uu____66905 = FStar_Util.physical_equality c1 c2  in
        if uu____66905
        then
          let uu____66912 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____66912
        else
          ((let uu____66936 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____66936
            then
              let uu____66941 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____66943 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____66941
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____66943
            else ());
           (let uu____66952 =
              let uu____66969 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____66980 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____66969, uu____66980)  in
            match uu____66952 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____67030),FStar_Syntax_Syntax.Total
                    (t2,uu____67032)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____67065 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____67065 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____67076,FStar_Syntax_Syntax.Total uu____67077) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____67104),FStar_Syntax_Syntax.Total
                    (t2,uu____67106)) ->
                     let uu____67139 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____67139 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____67151),FStar_Syntax_Syntax.GTotal
                    (t2,uu____67153)) ->
                     let uu____67186 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____67186 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____67198),FStar_Syntax_Syntax.GTotal
                    (t2,uu____67200)) ->
                     let uu____67233 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____67233 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____67244,FStar_Syntax_Syntax.Comp uu____67245) ->
                     let uu____67263 =
                       let uu___3573_67281 = problem  in
                       let uu____67299 =
                         let uu____67308 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____67308
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3573_67281.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____67299;
                         FStar_TypeChecker_Common.relation =
                           (uu___3573_67281.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3573_67281.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3573_67281.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3573_67281.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3573_67281.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3573_67281.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3573_67281.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3573_67281.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____67263 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____67368,FStar_Syntax_Syntax.Comp uu____67369) ->
                     let uu____67387 =
                       let uu___3573_67405 = problem  in
                       let uu____67423 =
                         let uu____67432 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____67432
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3573_67405.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____67423;
                         FStar_TypeChecker_Common.relation =
                           (uu___3573_67405.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3573_67405.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3573_67405.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3573_67405.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3573_67405.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3573_67405.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3573_67405.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3573_67405.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____67387 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____67492,FStar_Syntax_Syntax.GTotal uu____67493) ->
                     let uu____67511 =
                       let uu___3585_67529 = problem  in
                       let uu____67547 =
                         let uu____67556 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____67556
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3585_67529.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3585_67529.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3585_67529.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____67547;
                         FStar_TypeChecker_Common.element =
                           (uu___3585_67529.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3585_67529.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3585_67529.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3585_67529.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3585_67529.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3585_67529.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____67511 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____67616,FStar_Syntax_Syntax.Total uu____67617) ->
                     let uu____67635 =
                       let uu___3585_67653 = problem  in
                       let uu____67671 =
                         let uu____67680 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____67680
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3585_67653.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3585_67653.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3585_67653.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____67671;
                         FStar_TypeChecker_Common.element =
                           (uu___3585_67653.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3585_67653.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3585_67653.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3585_67653.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3585_67653.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3585_67653.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____67635 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____67740,FStar_Syntax_Syntax.Comp uu____67741) ->
                     let uu____67752 =
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
                     if uu____67752
                     then
                       let uu____67759 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____67759 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____67799 =
                            let uu____67814 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____67814
                            then (c1_comp, c2_comp)
                            else
                              (let uu____67843 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____67854 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____67843, uu____67854))
                             in
                          match uu____67799 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____67922 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____67922
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____67930 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____67930 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____67947 =
                                  let uu____67949 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____67951 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____67949 uu____67951
                                   in
                                giveup env uu____67947 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____67984 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____67984 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____68046 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____68046 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____68071 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____68102  ->
                match uu____68102 with
                | (u1,u2) ->
                    let uu____68110 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____68112 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____68110 uu____68112))
         in
      FStar_All.pipe_right uu____68071 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____68265,[])) when
          let uu____68292 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____68292 -> "{}"
      | uu____68295 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____68326 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____68326
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____68338 =
              FStar_List.map
                (fun uu____68351  ->
                   match uu____68351 with
                   | (uu____68358,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____68338 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____68369 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____68369 imps
  
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
                  let uu____68584 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____68584
                  then
                    let uu____68592 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____68594 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____68592
                      (rel_to_string rel) uu____68594
                  else "TOP"  in
                let uu____68600 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____68600 with
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
              let uu____68912 =
                let uu____68915 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _68918  -> FStar_Pervasives_Native.Some _68918)
                  uu____68915
                 in
              FStar_Syntax_Syntax.new_bv uu____68912 t1  in
            let uu____68919 =
              let uu____68932 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____68932
               in
            match uu____68919 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____69163 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____69163
         then
           let uu____69168 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____69168
         else ());
        (let uu____69175 =
           FStar_Util.record_time (fun uu____69182  -> solve env probs)  in
         match uu____69175 with
         | (sol,ms) ->
             ((let uu____69194 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____69194
               then
                 let uu____69199 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____69199
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____69212 =
                     FStar_Util.record_time
                       (fun uu____69219  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____69212 with
                    | ((),ms1) ->
                        ((let uu____69230 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____69230
                          then
                            let uu____69235 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____69235
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____69249 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____69249
                     then
                       let uu____69256 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____69256
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____69411 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____69411
            then
              let uu____69416 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____69416
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding true;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____69432 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____69432
             then
               let uu____69437 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____69437
             else ());
            (let f2 =
               let uu____69443 =
                 let uu____69444 = FStar_Syntax_Util.unmeta f1  in
                 uu____69444.FStar_Syntax_Syntax.n  in
               match uu____69443 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____69459 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3701_69460 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___3701_69460.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___3701_69460.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___3701_69460.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicit
        Prims.list) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____69667 =
              let uu____69676 =
                let uu____69685 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _69690  ->
                       FStar_TypeChecker_Common.NonTrivial _69690)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____69685;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____69676  in
            FStar_All.pipe_left
              (fun _69709  -> FStar_Pervasives_Native.Some _69709)
              uu____69667
  
let with_guard_no_simp :
  'Auu____69719 .
    'Auu____69719 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____69750 =
              let uu____69759 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _69764  -> FStar_TypeChecker_Common.NonTrivial _69764)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____69759;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____69750
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____69937 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____69937
           then
             let uu____69942 = FStar_Syntax_Print.term_to_string t1  in
             let uu____69944 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____69942
               uu____69944
           else ());
          (let uu____69949 =
             let uu____69962 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____69962
              in
           match uu____69949 with
           | (prob,wl) ->
               let g =
                 let uu____69999 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____70013  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____69999  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____70189 = try_teq true env t1 t2  in
        match uu____70189 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____70206 = FStar_TypeChecker_Env.get_range env  in
              let uu____70207 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____70206 uu____70207);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____70227 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____70227
              then
                let uu____70232 = FStar_Syntax_Print.term_to_string t1  in
                let uu____70234 = FStar_Syntax_Print.term_to_string t2  in
                let uu____70236 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____70232
                  uu____70234 uu____70236
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____70394 = FStar_TypeChecker_Env.get_range env  in
          let uu____70395 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____70394 uu____70395
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____70556 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____70556
         then
           let uu____70561 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____70563 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____70561 uu____70563
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____70574 =
           let uu____70604 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____70604 "sub_comp"
            in
         match uu____70574 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____70676 =
                 FStar_Util.record_time
                   (fun uu____70696  ->
                      let uu____70697 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____70712  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____70697)
                  in
               match uu____70676 with
               | (r,ms) ->
                   ((let uu____70763 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____70763
                     then
                       let uu____70768 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____70770 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____70772 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____70768 uu____70770
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____70772
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
      fun uu____70864  ->
        match uu____70864 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____70961 =
                 let uu____70967 =
                   let uu____70969 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____70971 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____70969 uu____70971
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____70967)  in
               let uu____70975 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____70961 uu____70975)
               in
            let equiv1 v1 v' =
              let uu____70988 =
                let uu____70993 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____70994 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____70993, uu____70994)  in
              match uu____70988 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____71018 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____71049 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____71049 with
                      | FStar_Syntax_Syntax.U_unif uu____71056 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____71087  ->
                                    match uu____71087 with
                                    | (u,v') ->
                                        let uu____71096 = equiv1 v1 v'  in
                                        if uu____71096
                                        then
                                          let uu____71101 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____71101 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____71122 -> []))
               in
            let uu____71127 =
              let wl =
                let uu___3792_71147 = empty_worklist env  in
                {
                  attempting = (uu___3792_71147.attempting);
                  wl_deferred = (uu___3792_71147.wl_deferred);
                  ctr = (uu___3792_71147.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3792_71147.smt_ok);
                  umax_heuristic_ok = (uu___3792_71147.umax_heuristic_ok);
                  tcenv = (uu___3792_71147.tcenv);
                  wl_implicits = (uu___3792_71147.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____71182  ->
                      match uu____71182 with
                      | (lb,v1) ->
                          let uu____71189 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____71189 with
                           | USolved wl1 -> ()
                           | uu____71200 -> fail1 lb v1)))
               in
            let rec check_ineq uu____71211 =
              match uu____71211 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____71223) -> true
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
                      uu____71255,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____71259,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____71272) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____71280,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____71289 -> false)
               in
            let uu____71295 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____71312  ->
                      match uu____71312 with
                      | (u,v1) ->
                          let uu____71320 = check_ineq (u, v1)  in
                          if uu____71320
                          then true
                          else
                            ((let uu____71328 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____71328
                              then
                                let uu____71333 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____71335 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____71333
                                  uu____71335
                              else ());
                             false)))
               in
            if uu____71295
            then ()
            else
              ((let uu____71345 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____71345
                then
                  ((let uu____71351 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____71351);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____71363 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____71363))
                else ());
               (let uu____71376 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____71376))
  
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
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____71678 =
          match uu____71678 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___3869_71720 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___3869_71720.attempting);
            wl_deferred = (uu___3869_71720.wl_deferred);
            ctr = (uu___3869_71720.ctr);
            defer_ok;
            smt_ok = (uu___3869_71720.smt_ok);
            umax_heuristic_ok = (uu___3869_71720.umax_heuristic_ok);
            tcenv = (uu___3869_71720.tcenv);
            wl_implicits = (uu___3869_71720.wl_implicits)
          }  in
        (let uu____71739 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____71739
         then
           let uu____71744 = FStar_Util.string_of_bool defer_ok  in
           let uu____71746 = wl_to_string wl  in
           let uu____71748 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____71744 uu____71746 uu____71748
         else ());
        (let g1 =
           let uu____71766 = solve_and_commit env wl fail1  in
           match uu____71766 with
           | FStar_Pervasives_Native.Some
               (uu____71777::uu____71778,uu____71779) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___3884_71812 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___3884_71812.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___3884_71812.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____71825 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___3889_71838 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___3889_71838.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___3889_71838.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___3889_71838.FStar_TypeChecker_Env.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____72237 = FStar_ST.op_Bang last_proof_ns  in
    match uu____72237 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.op_Colon_Equals last_proof_ns
             (FStar_Pervasives_Native.Some pns))
  
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
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
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___3908_72502 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___3908_72502.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___3908_72502.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___3908_72502.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____72511 =
            let uu____72513 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____72513  in
          if uu____72511
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____72545 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____72546 =
                       let uu____72548 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____72548
                        in
                     FStar_Errors.diag uu____72545 uu____72546)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding true;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____72565 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____72566 =
                        let uu____72568 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____72568
                         in
                      FStar_Errors.diag uu____72565 uu____72566)
                   else ();
                   (let uu____72574 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____72574
                      "discharge_guard'" env vc1);
                   (let uu____72576 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____72576 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____72601 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____72602 =
                                let uu____72604 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____72604
                                 in
                              FStar_Errors.diag uu____72601 uu____72602)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____72618 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____72619 =
                                let uu____72621 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____72621
                                 in
                              FStar_Errors.diag uu____72618 uu____72619)
                           else ();
                           (let vcs =
                              let uu____72693 = FStar_Options.use_tactics ()
                                 in
                              if uu____72693
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____72831  ->
                                     (let uu____72833 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____72833);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____73167  ->
                                              match uu____73167 with
                                              | (env1,goal,opts) ->
                                                  let uu____73415 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____73415, opts)))))
                              else
                                (let uu____73484 =
                                   let uu____73549 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____73549)  in
                                 [uu____73484])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____73872  ->
                                    match uu____73872 with
                                    | (env1,goal,opts) ->
                                        let uu____74056 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____74056 with
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
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____74072 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____74073 =
                                                   let uu____74075 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____74077 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____74075 uu____74077
                                                    in
                                                 FStar_Errors.diag
                                                   uu____74072 uu____74073)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____74084 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____74085 =
                                                   let uu____74087 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____74087
                                                    in
                                                 FStar_Errors.diag
                                                   uu____74084 uu____74085)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____74229 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____74229 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____74258 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____74258
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____74396 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____74396 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____74582 = try_teq false env t1 t2  in
        match uu____74582 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____74786 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____74786 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____74815 ->
                     let uu____74836 =
                       let uu____74837 = FStar_Syntax_Subst.compress r  in
                       uu____74837.FStar_Syntax_Syntax.n  in
                     (match uu____74836 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____74850) ->
                          unresolved ctx_u'
                      | uu____74883 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____74911 = acc  in
            match uu____74911 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____74950 = hd1  in
                     (match uu____74950 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____74981 = unresolved ctx_u  in
                             if uu____74981
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____75187 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____75187
                                     then
                                       let uu____75191 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____75191
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____75212 = teq_nosmt env1 t tm
                                          in
                                       match uu____75212 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4021_75262 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4021_75262.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4021_75262.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4021_75262.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4021_75262.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4021_75262.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4021_75262.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4021_75262.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4024_75298 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4024_75298.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4024_75298.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4024_75298.FStar_TypeChecker_Env.imp_range)
                                       }  in
                                     until_fixpoint (out, true) (hd2 ::
                                       (FStar_List.append extra tl1))))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4028_75433 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4028_75433.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4028_75433.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4028_75433.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4028_75433.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4028_75433.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4028_75433.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4028_75433.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4028_75433.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4028_75433.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4028_75433.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4028_75433.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4028_75433.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4028_75433.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4028_75433.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4028_75433.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4028_75433.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4028_75433.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4028_75433.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4028_75433.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4028_75433.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4028_75433.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4028_75433.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4028_75433.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4028_75433.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4028_75433.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4028_75433.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4028_75433.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4028_75433.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4028_75433.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4028_75433.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4028_75433.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4028_75433.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4028_75433.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4028_75433.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4028_75433.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4028_75433.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4028_75433.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4028_75433.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4028_75433.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4028_75433.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4028_75433.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4028_75433.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4033_75715 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4033_75715.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4033_75715.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4033_75715.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4033_75715.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4033_75715.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4033_75715.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4033_75715.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4033_75715.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4033_75715.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4033_75715.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4033_75715.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4033_75715.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4033_75715.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4033_75715.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4033_75715.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4033_75715.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4033_75715.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4033_75715.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4033_75715.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4033_75715.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4033_75715.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4033_75715.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4033_75715.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4033_75715.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4033_75715.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4033_75715.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4033_75715.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4033_75715.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4033_75715.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4033_75715.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4033_75715.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4033_75715.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4033_75715.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4033_75715.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4033_75715.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4033_75715.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4033_75715.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4033_75715.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4033_75715.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4033_75715.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4033_75715.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4033_75715.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____75828 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____75828
                                   then
                                     let uu____75833 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____75835 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____75837 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____75839 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____75833 uu____75835 uu____75837
                                       reason uu____75839
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4039_75858  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____75873 =
                                             let uu____75883 =
                                               let uu____75891 =
                                                 let uu____75893 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____75895 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____75897 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____75893 uu____75895
                                                   uu____75897
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____75891, r)
                                                in
                                             [uu____75883]  in
                                           FStar_Errors.add_errors
                                             uu____75873);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4047_75933 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4047_75933.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4047_75933.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4047_75933.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____75953 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____75968  ->
                                               let uu____75969 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____75971 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____75973 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____75969 uu____75971
                                                 reason uu____75973)) env2 g2
                                         true
                                        in
                                     match uu____75953 with
                                     | FStar_Pervasives_Native.Some g3 -> g3
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Env.implicits
                                         out), true) tl1)))))
             in
          let uu___4055_76005 = g  in
          let uu____76014 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4055_76005.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4055_76005.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4055_76005.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____76014
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____76429 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____76429 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____76450 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____76450
      | imp::uu____76464 ->
          let uu____76479 =
            let uu____76485 =
              let uu____76487 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____76489 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____76487 uu____76489 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____76485)
             in
          FStar_Errors.raise_error uu____76479
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____76635 = teq_nosmt env t1 t2  in
        match uu____76635 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4077_76678 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4077_76678.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4077_76678.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4077_76678.FStar_TypeChecker_Env.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____76855 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____76855
         then
           let uu____76860 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____76862 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____76860
             uu____76862
         else ());
        (let uu____76867 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____76867 with
         | (prob,x,wl) ->
             let g =
               let uu____76938 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____76953  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____76938  in
             ((let uu____76982 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____76982
               then
                 let uu____76991 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____76993 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____76995 =
                   let uu____76997 = FStar_Util.must g  in
                   guard_to_string env uu____76997  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____76991 uu____76993 uu____76995
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
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____77222 = check_subtyping env t1 t2  in
        match uu____77222 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____77294 =
              let uu____77303 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____77303 g  in
            FStar_Pervasives_Native.Some uu____77294
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____77454 = check_subtyping env t1 t2  in
        match uu____77454 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____77526 =
              let uu____77535 =
                let uu____77536 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____77536]  in
              FStar_TypeChecker_Env.close_guard env uu____77535 g  in
            FStar_Pervasives_Native.Some uu____77526
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____77721 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____77721
         then
           let uu____77726 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____77728 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____77726
             uu____77728
         else ());
        (let uu____77733 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____77733 with
         | (prob,x,wl) ->
             let g =
               let uu____77795 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____77810  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____77795  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____77870 =
                      let uu____77871 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____77871]  in
                    FStar_TypeChecker_Env.close_guard env uu____77870 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____78051 = subtype_nosmt env t1 t2  in
        match uu____78051 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  