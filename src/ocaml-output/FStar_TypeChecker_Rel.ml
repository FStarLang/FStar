open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____39 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____75 -> false
  
let (__proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
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
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
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
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                    FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,
                  worklist) FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                let ctx_uvar =
                  let uu____478 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____478;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
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
                     FStar_TypeChecker_Env.imp_range = r;
                     FStar_TypeChecker_Env.imp_meta =
                       FStar_Pervasives_Native.None
                   }  in
                 (ctx_uvar, t,
                   (let uu___355_514 = wl  in
                    {
                      attempting = (uu___355_514.attempting);
                      wl_deferred = (uu___355_514.wl_deferred);
                      ctr = (uu___355_514.ctr);
                      defer_ok = (uu___355_514.defer_ok);
                      smt_ok = (uu___355_514.smt_ok);
                      umax_heuristic_ok = (uu___355_514.umax_heuristic_ok);
                      tcenv = (uu___355_514.tcenv);
                      wl_implicits = (imp :: (wl.wl_implicits))
                    })))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,worklist)
            FStar_Pervasives_Native.tuple3)
  =
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___356_547 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___356_547.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___356_547.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___356_547.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___356_547.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___356_547.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___356_547.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___356_547.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___356_547.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___356_547.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___356_547.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___356_547.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___356_547.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___356_547.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___356_547.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___356_547.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___356_547.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___356_547.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___356_547.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___356_547.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___356_547.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___356_547.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___356_547.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___356_547.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___356_547.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___356_547.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___356_547.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___356_547.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___356_547.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___356_547.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___356_547.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___356_547.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___356_547.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___356_547.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___356_547.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___356_547.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___356_547.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___356_547.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___356_547.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___356_547.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___356_547.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___356_547.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___356_547.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____549 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____549 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____591 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____628 -> false
  
let (__proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____662 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____673 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____684 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___323_702  ->
    match uu___323_702 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____714 = FStar_Syntax_Util.head_and_args t  in
    match uu____714 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____777 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____779 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____794 =
                     let uu____796 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____796  in
                   FStar_Util.format1 "@<%s>" uu____794
                in
             let uu____800 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____777 uu____779 uu____800
         | uu____803 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___324_815  ->
      match uu___324_815 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____820 =
            let uu____824 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____826 =
              let uu____830 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____832 =
                let uu____836 =
                  let uu____840 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____840]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____836
                 in
              uu____830 :: uu____832  in
            uu____824 :: uu____826  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____820
      | FStar_TypeChecker_Common.CProb p ->
          let uu____851 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____853 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____855 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____851 uu____853
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____855
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___325_869  ->
      match uu___325_869 with
      | UNIV (u,t) ->
          let x =
            let uu____875 = FStar_Options.hide_uvar_nums ()  in
            if uu____875
            then "?"
            else
              (let uu____882 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____882 FStar_Util.string_of_int)
             in
          let uu____886 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____886
      | TERM (u,t) ->
          let x =
            let uu____893 = FStar_Options.hide_uvar_nums ()  in
            if uu____893
            then "?"
            else
              (let uu____900 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____900 FStar_Util.string_of_int)
             in
          let uu____904 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____904
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____923 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____923 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____944 =
      let uu____948 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____948
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____944 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____967 .
    (FStar_Syntax_Syntax.term,'Auu____967) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____986 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1007  ->
              match uu____1007 with
              | (x,uu____1014) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____986 (FStar_String.concat " ")
  
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
        (let uu____1057 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1057
         then
           let uu____1062 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1062
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___326_1073  ->
    match uu___326_1073 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1079 .
    'Auu____1079 FStar_TypeChecker_Common.problem ->
      'Auu____1079 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___357_1091 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___357_1091.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___357_1091.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___357_1091.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___357_1091.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___357_1091.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___357_1091.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___357_1091.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1099 .
    'Auu____1099 FStar_TypeChecker_Common.problem ->
      'Auu____1099 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___327_1119  ->
    match uu___327_1119 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_1  -> FStar_TypeChecker_Common.TProb _0_1)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_2  -> FStar_TypeChecker_Common.CProb _0_2)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___328_1135  ->
    match uu___328_1135 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___358_1141 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___358_1141.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___358_1141.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___358_1141.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___358_1141.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___358_1141.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___358_1141.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___358_1141.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___358_1141.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___358_1141.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___359_1149 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___359_1149.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___359_1149.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___359_1149.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___359_1149.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___359_1149.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___359_1149.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___359_1149.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___359_1149.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___359_1149.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___329_1162  ->
      match uu___329_1162 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___330_1169  ->
    match uu___330_1169 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___331_1182  ->
    match uu___331_1182 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___332_1197  ->
    match uu___332_1197 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___333_1212  ->
    match uu___333_1212 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___334_1226  ->
    match uu___334_1226 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___335_1240  ->
    match uu___335_1240 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___336_1252  ->
    match uu___336_1252 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1268 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1268) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1298 =
          let uu____1300 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1300  in
        if uu____1298
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1337)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1384 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1408 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1408]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1384
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1436 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1460 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1460]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1436
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1507 =
          let uu____1509 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1509  in
        if uu____1507
        then ()
        else
          (let uu____1514 =
             let uu____1517 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1517
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1514 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1566 =
          let uu____1568 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1568  in
        if uu____1566
        then ()
        else
          (let uu____1573 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1573)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1593 =
        let uu____1595 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1595  in
      if uu____1593
      then ()
      else
        (let msgf m =
           let uu____1609 =
             let uu____1611 =
               let uu____1613 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1613 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1611  in
           Prims.strcat msg uu____1609  in
         (let uu____1618 = msgf "scope"  in
          let uu____1621 = p_scope prob  in
          def_scope_wf uu____1618 (p_loc prob) uu____1621);
         (let uu____1633 = msgf "guard"  in
          def_check_scoped uu____1633 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1640 = msgf "lhs"  in
                def_check_scoped uu____1640 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1643 = msgf "rhs"  in
                def_check_scoped uu____1643 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1650 = msgf "lhs"  in
                def_check_scoped_comp uu____1650 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1653 = msgf "rhs"  in
                def_check_scoped_comp uu____1653 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___360_1674 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___360_1674.wl_deferred);
          ctr = (uu___360_1674.ctr);
          defer_ok = (uu___360_1674.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___360_1674.umax_heuristic_ok);
          tcenv = (uu___360_1674.tcenv);
          wl_implicits = (uu___360_1674.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1682 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1682,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___361_1705 = empty_worklist env  in
      let uu____1706 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1706;
        wl_deferred = (uu___361_1705.wl_deferred);
        ctr = (uu___361_1705.ctr);
        defer_ok = (uu___361_1705.defer_ok);
        smt_ok = (uu___361_1705.smt_ok);
        umax_heuristic_ok = (uu___361_1705.umax_heuristic_ok);
        tcenv = (uu___361_1705.tcenv);
        wl_implicits = (uu___361_1705.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___362_1729 = wl  in
        {
          attempting = (uu___362_1729.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___362_1729.ctr);
          defer_ok = (uu___362_1729.defer_ok);
          smt_ok = (uu___362_1729.smt_ok);
          umax_heuristic_ok = (uu___362_1729.umax_heuristic_ok);
          tcenv = (uu___362_1729.tcenv);
          wl_implicits = (uu___362_1729.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___363_1757 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___363_1757.wl_deferred);
         ctr = (uu___363_1757.ctr);
         defer_ok = (uu___363_1757.defer_ok);
         smt_ok = (uu___363_1757.smt_ok);
         umax_heuristic_ok = (uu___363_1757.umax_heuristic_ok);
         tcenv = (uu___363_1757.tcenv);
         wl_implicits = (uu___363_1757.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1771 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1771 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term ->
              (FStar_Syntax_Syntax.term,worklist)
                FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1805 = FStar_Syntax_Util.type_u ()  in
            match uu____1805 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1817 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                   in
                (match uu____1817 with
                 | (uu____1829,tt,wl1) ->
                     let uu____1832 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1832, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___337_1838  ->
    match uu___337_1838 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_3  -> FStar_TypeChecker_Common.TProb _0_3) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_4  -> FStar_TypeChecker_Common.CProb _0_4) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1856 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1856 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1876  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1973 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1973 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1973 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1973 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
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
                        let uu____2060 =
                          let uu____2069 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2069]  in
                        FStar_List.append scope uu____2060
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2112 =
                      let uu____2115 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2115  in
                    FStar_List.append uu____2112
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2134 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2134 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2154 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2154;
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
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu____2228 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2228 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.strcat reason ".mk_c.arg") orig;
                  (let uu____2316 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2316 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2354 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2354 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2354 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2354 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
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
                          let uu____2422 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2422]  in
                        let uu____2441 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2441
                     in
                  let uu____2444 =
                    let uu____2451 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___364_2462 = wl  in
                       {
                         attempting = (uu___364_2462.attempting);
                         wl_deferred = (uu___364_2462.wl_deferred);
                         ctr = (uu___364_2462.ctr);
                         defer_ok = (uu___364_2462.defer_ok);
                         smt_ok = (uu___364_2462.smt_ok);
                         umax_heuristic_ok =
                           (uu___364_2462.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___364_2462.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2451
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2444 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2474 =
                              let uu____2479 =
                                let uu____2480 =
                                  let uu____2489 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2489
                                   in
                                [uu____2480]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2479  in
                            uu____2474 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2519 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2519;
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
                let uu____2567 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2567;
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
  'Auu____2582 .
    worklist ->
      'Auu____2582 FStar_TypeChecker_Common.problem ->
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
              let uu____2615 =
                let uu____2618 =
                  let uu____2619 =
                    let uu____2626 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2626)  in
                  FStar_Syntax_Syntax.NT uu____2619  in
                [uu____2618]  in
              FStar_Syntax_Subst.subst uu____2615 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2650 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2650
        then
          let uu____2658 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2661 = prob_to_string env d  in
          let uu____2663 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2658 uu____2661 uu____2663 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2679 -> failwith "impossible"  in
           let uu____2682 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2698 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2700 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2698, uu____2700)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2707 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2709 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2707, uu____2709)
              in
           match uu____2682 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___338_2737  ->
            match uu___338_2737 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2749 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2753 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2753 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___339_2784  ->
           match uu___339_2784 with
           | UNIV uu____2787 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2794 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2794
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
        (fun uu___340_2822  ->
           match uu___340_2822 with
           | UNIV (u',t) ->
               let uu____2827 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2827
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2834 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2846 =
        let uu____2847 =
          let uu____2848 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2848
           in
        FStar_Syntax_Subst.compress uu____2847  in
      FStar_All.pipe_right uu____2846 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2860 =
        let uu____2861 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t
           in
        FStar_Syntax_Subst.compress uu____2861  in
      FStar_All.pipe_right uu____2860 FStar_Syntax_Util.unlazy_emb
  
let norm_arg :
  'Auu____2869 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2869) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2869)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2892 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2892, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____2944  ->
              match uu____2944 with
              | (x,imp) ->
                  let uu____2963 =
                    let uu___365_2964 = x  in
                    let uu____2965 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___365_2964.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___365_2964.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2965
                    }  in
                  (uu____2963, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2989 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2989
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2993 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2993
        | uu____2996 -> u2  in
      let uu____2997 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2997
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                    FStar_Pervasives_Native.tuple2
                                    FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
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
                (let uu____3118 = norm_refinement env t12  in
                 match uu____3118 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3133;
                     FStar_Syntax_Syntax.vars = uu____3134;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3158 =
                       let uu____3160 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3162 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3160 uu____3162
                        in
                     failwith uu____3158)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3178 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3178
          | FStar_Syntax_Syntax.Tm_uinst uu____3179 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3216 =
                   let uu____3217 = FStar_Syntax_Subst.compress t1'  in
                   uu____3217.FStar_Syntax_Syntax.n  in
                 match uu____3216 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3232 -> aux true t1'
                 | uu____3240 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3255 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3286 =
                   let uu____3287 = FStar_Syntax_Subst.compress t1'  in
                   uu____3287.FStar_Syntax_Syntax.n  in
                 match uu____3286 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3302 -> aux true t1'
                 | uu____3310 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3325 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3372 =
                   let uu____3373 = FStar_Syntax_Subst.compress t1'  in
                   uu____3373.FStar_Syntax_Syntax.n  in
                 match uu____3372 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3388 -> aux true t1'
                 | uu____3396 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3411 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3426 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3441 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3456 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3471 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3500 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3533 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3554 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3581 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3609 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3646 ->
              let uu____3653 =
                let uu____3655 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3657 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3655 uu____3657
                 in
              failwith uu____3653
          | FStar_Syntax_Syntax.Tm_ascribed uu____3672 ->
              let uu____3699 =
                let uu____3701 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3703 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3701 uu____3703
                 in
              failwith uu____3699
          | FStar_Syntax_Syntax.Tm_delayed uu____3718 ->
              let uu____3741 =
                let uu____3743 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3745 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3743 uu____3745
                 in
              failwith uu____3741
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3760 =
                let uu____3762 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3764 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3762 uu____3764
                 in
              failwith uu____3760
           in
        let uu____3779 = whnf env t1  in aux false uu____3779
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
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
      let uu____3840 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3840 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3881 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3881, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____3908 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3908 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                          FStar_Syntax_Syntax.term)
                                                          FStar_Pervasives_Native.tuple2
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun uu____3968  ->
    match uu____3968 with
    | (t_base,refopt) ->
        let uu____3999 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3999 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4041 =
      let uu____4045 =
        let uu____4048 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4075  ->
                  match uu____4075 with | (uu____4084,uu____4085,x) -> x))
           in
        FStar_List.append wl.attempting uu____4048  in
      FStar_List.map (wl_prob_to_string wl) uu____4045  in
    FStar_All.pipe_right uu____4041 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4108 .
    ('Auu____4108,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4120  ->
    match uu____4120 with
    | (uu____4127,c,args) ->
        let uu____4130 = print_ctx_uvar c  in
        let uu____4132 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4130 uu____4132
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4142 = FStar_Syntax_Util.head_and_args t  in
    match uu____4142 with
    | (head1,_args) ->
        let uu____4186 =
          let uu____4187 = FStar_Syntax_Subst.compress head1  in
          uu____4187.FStar_Syntax_Syntax.n  in
        (match uu____4186 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4191 -> true
         | uu____4205 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4213 = FStar_Syntax_Util.head_and_args t  in
    match uu____4213 with
    | (head1,_args) ->
        let uu____4256 =
          let uu____4257 = FStar_Syntax_Subst.compress head1  in
          uu____4257.FStar_Syntax_Syntax.n  in
        (match uu____4256 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4261) -> u
         | uu____4278 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4303 = FStar_Syntax_Util.head_and_args t  in
      match uu____4303 with
      | (head1,args) ->
          let uu____4350 =
            let uu____4351 = FStar_Syntax_Subst.compress head1  in
            uu____4351.FStar_Syntax_Syntax.n  in
          (match uu____4350 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4359)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4392 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___341_4417  ->
                         match uu___341_4417 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4422 =
                               let uu____4423 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4423.FStar_Syntax_Syntax.n  in
                             (match uu____4422 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4428 -> false)
                         | uu____4430 -> true))
                  in
               (match uu____4392 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4455 =
                        FStar_List.collect
                          (fun uu___342_4467  ->
                             match uu___342_4467 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4471 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4471]
                             | uu____4472 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4455 FStar_List.rev  in
                    let uu____4495 =
                      let uu____4502 =
                        let uu____4511 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___343_4533  ->
                                  match uu___343_4533 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4537 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4537]
                                  | uu____4538 -> []))
                           in
                        FStar_All.pipe_right uu____4511 FStar_List.rev  in
                      let uu____4561 =
                        let uu____4564 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4564  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4502 uu____4561
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4495 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4600  ->
                                match uu____4600 with
                                | (x,i) ->
                                    let uu____4619 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4619, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4650  ->
                                match uu____4650 with
                                | (a,i) ->
                                    let uu____4669 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4669, i)) args_sol
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
           | uu____4691 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4713 =
          let uu____4736 =
            let uu____4737 = FStar_Syntax_Subst.compress k  in
            uu____4737.FStar_Syntax_Syntax.n  in
          match uu____4736 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4819 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4819)
              else
                (let uu____4854 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4854 with
                 | (ys',t1,uu____4887) ->
                     let uu____4892 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4892))
          | uu____4931 ->
              let uu____4932 =
                let uu____4937 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4937)  in
              ((ys, t), uu____4932)
           in
        match uu____4713 with
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
                 let uu____5032 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5032 c  in
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
               (let uu____5110 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5110
                then
                  let uu____5115 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5117 = print_ctx_uvar uv  in
                  let uu____5119 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5115 uu____5117 uu____5119
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5128 =
                   let uu____5130 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____5130  in
                 let uu____5133 =
                   let uu____5136 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5136
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5128 uu____5133 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5169 =
               let uu____5170 =
                 let uu____5172 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5174 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5172 uu____5174
                  in
               failwith uu____5170  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5240  ->
                       match uu____5240 with
                       | (a,i) ->
                           let uu____5261 =
                             let uu____5262 = FStar_Syntax_Subst.compress a
                                in
                             uu____5262.FStar_Syntax_Syntax.n  in
                           (match uu____5261 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5288 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5298 =
                 let uu____5300 = is_flex g  in Prims.op_Negation uu____5300
                  in
               if uu____5298
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5309 = destruct_flex_t g wl  in
                  match uu____5309 with
                  | ((uu____5314,uv1,args),wl1) ->
                      ((let uu____5319 = args_as_binders args  in
                        assign_solution uu____5319 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___366_5321 = wl1  in
              {
                attempting = (uu___366_5321.attempting);
                wl_deferred = (uu___366_5321.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___366_5321.defer_ok);
                smt_ok = (uu___366_5321.smt_ok);
                umax_heuristic_ok = (uu___366_5321.umax_heuristic_ok);
                tcenv = (uu___366_5321.tcenv);
                wl_implicits = (uu___366_5321.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5346 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5346
         then
           let uu____5351 = FStar_Util.string_of_int pid  in
           let uu____5353 =
             let uu____5355 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5355 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5351 uu____5353
         else ());
        commit sol;
        (let uu___367_5369 = wl  in
         {
           attempting = (uu___367_5369.attempting);
           wl_deferred = (uu___367_5369.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___367_5369.defer_ok);
           smt_ok = (uu___367_5369.smt_ok);
           umax_heuristic_ok = (uu___367_5369.umax_heuristic_ok);
           tcenv = (uu___367_5369.tcenv);
           wl_implicits = (uu___367_5369.wl_implicits)
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
             | (uu____5435,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5463 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5463
              in
           (let uu____5469 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5469
            then
              let uu____5474 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5478 =
                let uu____5480 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5480 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5474 uu____5478
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____5515 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5515 FStar_Util.set_elements  in
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
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool,Prims.string
                                                            FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun uk  ->
    fun t  ->
      let uu____5555 = occurs uk t  in
      match uu____5555 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5594 =
                 let uu____5596 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5598 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5596 uu____5598
                  in
               FStar_Pervasives_Native.Some uu____5594)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,(FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.binders)
                                     FStar_Pervasives_Native.tuple2)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____5718 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5718 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5769 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5826  ->
             match uu____5826 with
             | (x,uu____5838) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5856 = FStar_List.last bs  in
      match uu____5856 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5880) ->
          let uu____5891 =
            FStar_Util.prefix_until
              (fun uu___344_5906  ->
                 match uu___344_5906 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5909 -> false) g
             in
          (match uu____5891 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5923,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5960 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5960 with
        | (pfx,uu____5970) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5982 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5982 with
             | (uu____5989,src',wl1) ->
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
                 | uu____6103 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6104 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6168  ->
                  fun uu____6169  ->
                    match (uu____6168, uu____6169) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6272 =
                          let uu____6274 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6274
                           in
                        if uu____6272
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6308 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6308
                           then
                             let uu____6325 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6325)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6104 with | (isect,uu____6375) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6411 'Auu____6412 .
    (FStar_Syntax_Syntax.bv,'Auu____6411) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____6412) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6470  ->
              fun uu____6471  ->
                match (uu____6470, uu____6471) with
                | ((a,uu____6490),(b,uu____6492)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6508 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6508) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6539  ->
           match uu____6539 with
           | (y,uu____6546) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6556 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6556) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                    FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2 Prims.list ->
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
                   let uu____6718 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6718
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6751 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____6803 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6848 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6870 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___345_6878  ->
    match uu___345_6878 with
    | MisMatch (d1,d2) ->
        let uu____6890 =
          let uu____6892 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6894 =
            let uu____6896 =
              let uu____6898 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6898 ")"  in
            Prims.strcat ") (" uu____6896  in
          Prims.strcat uu____6892 uu____6894  in
        Prims.strcat "MisMatch (" uu____6890
    | HeadMatch u ->
        let uu____6905 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6905
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___346_6914  ->
    match uu___346_6914 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6931 -> HeadMatch false
  
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
          let uu____6953 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6953 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6964 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6988 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6998 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7025 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7025
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7026 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7027 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7028 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7041 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7055 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7079) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7085,uu____7086) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7128) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7153;
             FStar_Syntax_Syntax.index = uu____7154;
             FStar_Syntax_Syntax.sort = t2;_},uu____7156)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7164 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7165 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7166 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7181 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7188 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7208 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7208
  
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
           { FStar_Syntax_Syntax.blob = uu____7227;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7228;
             FStar_Syntax_Syntax.ltyp = uu____7229;
             FStar_Syntax_Syntax.rng = uu____7230;_},uu____7231)
            ->
            let uu____7242 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7242 t21
        | (uu____7243,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7244;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7245;
             FStar_Syntax_Syntax.ltyp = uu____7246;
             FStar_Syntax_Syntax.rng = uu____7247;_})
            ->
            let uu____7258 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7258
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7270 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7270
            then FullMatch
            else
              (let uu____7275 =
                 let uu____7284 =
                   let uu____7287 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7287  in
                 let uu____7288 =
                   let uu____7291 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7291  in
                 (uu____7284, uu____7288)  in
               MisMatch uu____7275)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7297),FStar_Syntax_Syntax.Tm_uinst (g,uu____7299)) ->
            let uu____7308 = head_matches env f g  in
            FStar_All.pipe_right uu____7308 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7311 = FStar_Const.eq_const c d  in
            if uu____7311
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7321),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7323)) ->
            let uu____7356 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7356
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7366),FStar_Syntax_Syntax.Tm_refine (y,uu____7368)) ->
            let uu____7377 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7377 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7379),uu____7380) ->
            let uu____7385 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7385 head_match
        | (uu____7386,FStar_Syntax_Syntax.Tm_refine (x,uu____7388)) ->
            let uu____7393 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7393 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7394,FStar_Syntax_Syntax.Tm_type
           uu____7395) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7397,FStar_Syntax_Syntax.Tm_arrow uu____7398) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7429),FStar_Syntax_Syntax.Tm_app (head',uu____7431))
            ->
            let uu____7480 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7480 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7482),uu____7483) ->
            let uu____7508 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7508 head_match
        | (uu____7509,FStar_Syntax_Syntax.Tm_app (head1,uu____7511)) ->
            let uu____7536 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7536 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7537,FStar_Syntax_Syntax.Tm_let
           uu____7538) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7566,FStar_Syntax_Syntax.Tm_match uu____7567) ->
            HeadMatch true
        | uu____7613 ->
            let uu____7618 =
              let uu____7627 = delta_depth_of_term env t11  in
              let uu____7630 = delta_depth_of_term env t21  in
              (uu____7627, uu____7630)  in
            MisMatch uu____7618
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    worklist ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                          FStar_Pervasives_Native.tuple2
                          FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let head1 = FStar_Syntax_Util.head_of t  in
            (let uu____7696 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7696
             then
               let uu____7701 = FStar_Syntax_Print.term_to_string t  in
               let uu____7703 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7701 uu____7703
             else ());
            (let uu____7708 =
               let uu____7709 = FStar_Syntax_Util.un_uinst head1  in
               uu____7709.FStar_Syntax_Syntax.n  in
             match uu____7708 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7715 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7715 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7729 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7729
                        then
                          let uu____7734 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7734
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7739 ->
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
                        FStar_TypeChecker_Normalize.normalize steps env t  in
                      let uu____7756 =
                        let uu____7758 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7758 = FStar_Syntax_Util.Equal  in
                      if uu____7756
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7765 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7765
                          then
                            let uu____7770 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7772 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7770
                              uu____7772
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7777 -> FStar_Pervasives_Native.None)
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
            (let uu____7929 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7929
             then
               let uu____7934 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7936 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7938 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7934
                 uu____7936 uu____7938
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7966 =
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
               match uu____7966 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8014 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8014 with
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
                  uu____8052),uu____8053)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8074 =
                      let uu____8083 = maybe_inline t11  in
                      let uu____8086 = maybe_inline t21  in
                      (uu____8083, uu____8086)  in
                    match uu____8074 with
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
                 (uu____8129,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8130))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8151 =
                      let uu____8160 = maybe_inline t11  in
                      let uu____8163 = maybe_inline t21  in
                      (uu____8160, uu____8163)  in
                    match uu____8151 with
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
             | MisMatch uu____8218 -> fail1 n_delta r t11 t21
             | uu____8227 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____8242 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8242
           then
             let uu____8247 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8249 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8251 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8259 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8276 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8276
                    (fun uu____8311  ->
                       match uu____8311 with
                       | (t11,t21) ->
                           let uu____8319 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8321 =
                             let uu____8323 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____8323  in
                           Prims.strcat uu____8319 uu____8321))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8247 uu____8249 uu____8251 uu____8259
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8340 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8340 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___347_8355  ->
    match uu___347_8355 with
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
      let uu___368_8404 = p  in
      let uu____8407 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8408 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___368_8404.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8407;
        FStar_TypeChecker_Common.relation =
          (uu___368_8404.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8408;
        FStar_TypeChecker_Common.element =
          (uu___368_8404.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___368_8404.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___368_8404.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___368_8404.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___368_8404.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___368_8404.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8423 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8423
            (fun _0_5  -> FStar_TypeChecker_Common.TProb _0_5)
      | FStar_TypeChecker_Common.CProb uu____8428 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8451 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8451 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8459 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8459 with
           | (lh,lhs_args) ->
               let uu____8506 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8506 with
                | (rh,rhs_args) ->
                    let uu____8553 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8566,FStar_Syntax_Syntax.Tm_uvar uu____8567)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8656 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8683,uu____8684)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8699,FStar_Syntax_Syntax.Tm_uvar uu____8700)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8715,FStar_Syntax_Syntax.Tm_arrow uu____8716)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___369_8746 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___369_8746.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___369_8746.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___369_8746.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___369_8746.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___369_8746.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___369_8746.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___369_8746.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___369_8746.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___369_8746.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8749,FStar_Syntax_Syntax.Tm_type uu____8750)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___369_8766 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___369_8766.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___369_8766.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___369_8766.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___369_8766.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___369_8766.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___369_8766.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___369_8766.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___369_8766.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___369_8766.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8769,FStar_Syntax_Syntax.Tm_uvar uu____8770)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___369_8786 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___369_8786.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___369_8786.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___369_8786.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___369_8786.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___369_8786.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___369_8786.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___369_8786.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___369_8786.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___369_8786.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8789,FStar_Syntax_Syntax.Tm_uvar uu____8790)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8805,uu____8806)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8821,FStar_Syntax_Syntax.Tm_uvar uu____8822)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8837,uu____8838) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8553 with
                     | (rank,tp1) ->
                         let uu____8851 =
                           FStar_All.pipe_right
                             (let uu___370_8855 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___370_8855.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___370_8855.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___370_8855.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___370_8855.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___370_8855.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___370_8855.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___370_8855.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___370_8855.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___370_8855.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_6  ->
                                FStar_TypeChecker_Common.TProb _0_6)
                            in
                         (rank, uu____8851))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8861 =
            FStar_All.pipe_right
              (let uu___371_8865 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___371_8865.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___371_8865.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___371_8865.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___371_8865.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___371_8865.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___371_8865.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___371_8865.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___371_8865.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___371_8865.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_7  -> FStar_TypeChecker_Common.CProb _0_7)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8861)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8927 probs =
      match uu____8927 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9008 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9029 = rank wl.tcenv hd1  in
               (match uu____9029 with
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
                      (let uu____9090 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9095 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9095)
                          in
                       if uu____9090
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
          let uu____9168 = FStar_Syntax_Util.head_and_args t  in
          match uu____9168 with
          | (hd1,uu____9187) ->
              let uu____9212 =
                let uu____9213 = FStar_Syntax_Subst.compress hd1  in
                uu____9213.FStar_Syntax_Syntax.n  in
              (match uu____9212 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9218) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9253  ->
                           match uu____9253 with
                           | (y,uu____9262) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9285  ->
                                       match uu____9285 with
                                       | (x,uu____9294) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9299 -> false)
           in
        let uu____9301 = rank tcenv p  in
        match uu____9301 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9310 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9347 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9367 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9388 -> false
  
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
                        let uu____9451 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9451 with
                        | (k,uu____9459) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9472 -> false)))
            | uu____9474 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9526 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9534 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9534 = (Prims.parse_int "0")))
                           in
                        if uu____9526 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9555 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9563 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9563 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9555)
               in
            let uu____9567 = filter1 u12  in
            let uu____9570 = filter1 u22  in (uu____9567, uu____9570)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9605 = filter_out_common_univs us1 us2  in
                   (match uu____9605 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9665 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9665 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9668 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____9679 =
                             let uu____9681 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____9683 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____9681 uu____9683
                              in
                           UFailed uu____9679))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9709 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9709 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9735 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9735 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9738 ->
                   let uu____9743 =
                     let uu____9745 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____9747 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____9745
                       uu____9747 msg
                      in
                   UFailed uu____9743)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9750,uu____9751) ->
              let uu____9753 =
                let uu____9755 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9757 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9755 uu____9757
                 in
              failwith uu____9753
          | (FStar_Syntax_Syntax.U_unknown ,uu____9760) ->
              let uu____9761 =
                let uu____9763 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9765 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9763 uu____9765
                 in
              failwith uu____9761
          | (uu____9768,FStar_Syntax_Syntax.U_bvar uu____9769) ->
              let uu____9771 =
                let uu____9773 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9775 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9773 uu____9775
                 in
              failwith uu____9771
          | (uu____9778,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9779 =
                let uu____9781 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9783 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9781 uu____9783
                 in
              failwith uu____9779
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9813 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9813
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9830 = occurs_univ v1 u3  in
              if uu____9830
              then
                let uu____9833 =
                  let uu____9835 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9837 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9835 uu____9837
                   in
                try_umax_components u11 u21 uu____9833
              else
                (let uu____9842 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9842)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9854 = occurs_univ v1 u3  in
              if uu____9854
              then
                let uu____9857 =
                  let uu____9859 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9861 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9859 uu____9861
                   in
                try_umax_components u11 u21 uu____9857
              else
                (let uu____9866 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9866)
          | (FStar_Syntax_Syntax.U_max uu____9867,uu____9868) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9876 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9876
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9882,FStar_Syntax_Syntax.U_max uu____9883) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9891 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9891
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9897,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9899,FStar_Syntax_Syntax.U_name
             uu____9900) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9902) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9904) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9906,FStar_Syntax_Syntax.U_succ
             uu____9907) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9909,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
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
    ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list,'b) FStar_Pervasives_Native.tuple2,('a Prims.list,
                                                             'b)
                                                             FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun bc1  ->
    fun bc2  ->
      let uu____10016 = bc1  in
      match uu____10016 with
      | (bs1,mk_cod1) ->
          let uu____10060 = bc2  in
          (match uu____10060 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10171 = aux xs ys  in
                     (match uu____10171 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10254 =
                       let uu____10261 = mk_cod1 xs  in ([], uu____10261)  in
                     let uu____10264 =
                       let uu____10271 = mk_cod2 ys  in ([], uu____10271)  in
                     (uu____10254, uu____10264)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____10340 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10340 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10343 =
                    let uu____10344 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10344 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10343
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10349 = has_type_guard t1 t2  in (uu____10349, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10350 = has_type_guard t2 t1  in (uu____10350, wl)
  
let is_flex_pat :
  'Auu____10360 'Auu____10361 'Auu____10362 .
    ('Auu____10360,'Auu____10361,'Auu____10362 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___348_10376  ->
    match uu___348_10376 with
    | (uu____10385,uu____10386,[]) -> true
    | uu____10390 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10423 = f  in
      match uu____10423 with
      | (uu____10430,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10431;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10432;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10435;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10436;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10437;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10499  ->
                 match uu____10499 with
                 | (y,uu____10508) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10662 =
                  let uu____10677 =
                    let uu____10680 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10680  in
                  ((FStar_List.rev pat_binders), uu____10677)  in
                FStar_Pervasives_Native.Some uu____10662
            | (uu____10713,[]) ->
                let uu____10744 =
                  let uu____10759 =
                    let uu____10762 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10762  in
                  ((FStar_List.rev pat_binders), uu____10759)  in
                FStar_Pervasives_Native.Some uu____10744
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____10853 =
                  let uu____10854 = FStar_Syntax_Subst.compress a  in
                  uu____10854.FStar_Syntax_Syntax.n  in
                (match uu____10853 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10874 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____10874
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___372_10904 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___372_10904.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___372_10904.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____10908 =
                            let uu____10909 =
                              let uu____10916 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____10916)  in
                            FStar_Syntax_Syntax.NT uu____10909  in
                          [uu____10908]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___373_10932 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___373_10932.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___373_10932.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10933 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____10973 =
                  let uu____10988 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10988  in
                (match uu____10973 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11063 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11096 ->
               let uu____11097 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11097 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11419 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11419
       then
         let uu____11424 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11424
       else ());
      (let uu____11429 = next_prob probs  in
       match uu____11429 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___374_11456 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___374_11456.wl_deferred);
               ctr = (uu___374_11456.ctr);
               defer_ok = (uu___374_11456.defer_ok);
               smt_ok = (uu___374_11456.smt_ok);
               umax_heuristic_ok = (uu___374_11456.umax_heuristic_ok);
               tcenv = (uu___374_11456.tcenv);
               wl_implicits = (uu___374_11456.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11465 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11465
                 then
                   let uu____11468 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11468
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t' env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t' env
                           (let uu___375_11480 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___375_11480.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___375_11480.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___375_11480.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___375_11480.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___375_11480.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___375_11480.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___375_11480.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___375_11480.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___375_11480.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11506 ->
                let uu____11517 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11588  ->
                          match uu____11588 with
                          | (c,uu____11599,uu____11600) -> c < probs.ctr))
                   in
                (match uu____11517 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11655 =
                            let uu____11660 =
                              FStar_List.map
                                (fun uu____11678  ->
                                   match uu____11678 with
                                   | (uu____11692,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____11660, (probs.wl_implicits))  in
                          Success uu____11655
                      | uu____11700 ->
                          let uu____11711 =
                            let uu___376_11712 = probs  in
                            let uu____11713 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11736  ->
                                      match uu____11736 with
                                      | (uu____11745,uu____11746,y) -> y))
                               in
                            {
                              attempting = uu____11713;
                              wl_deferred = rest;
                              ctr = (uu___376_11712.ctr);
                              defer_ok = (uu___376_11712.defer_ok);
                              smt_ok = (uu___376_11712.smt_ok);
                              umax_heuristic_ok =
                                (uu___376_11712.umax_heuristic_ok);
                              tcenv = (uu___376_11712.tcenv);
                              wl_implicits = (uu___376_11712.wl_implicits)
                            }  in
                          solve env uu____11711))))

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
            let uu____11757 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11757 with
            | USolved wl1 ->
                let uu____11759 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11759
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
                  let uu____11813 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11813 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11816 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11829;
                  FStar_Syntax_Syntax.vars = uu____11830;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11833;
                  FStar_Syntax_Syntax.vars = uu____11834;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11847,uu____11848) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11856,FStar_Syntax_Syntax.Tm_uinst uu____11857) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11865 -> USolved wl

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
            ((let uu____11877 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____11877
              then
                let uu____11882 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11882 msg
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
               let uu____11974 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____11974 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12029 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12029
                then
                  let uu____12034 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12036 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12034 uu____12036
                else ());
               (let uu____12041 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12041 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12087 = eq_prob t1 t2 wl2  in
                         (match uu____12087 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12108 ->
                         let uu____12117 = eq_prob t1 t2 wl2  in
                         (match uu____12117 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12167 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12182 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12183 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12182, uu____12183)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12188 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12189 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12188, uu____12189)
                            in
                         (match uu____12167 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12220 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12220 with
                                | (t1_hd,t1_args) ->
                                    let uu____12265 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12265 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12331 =
                                              let uu____12338 =
                                                let uu____12349 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12349 :: t1_args  in
                                              let uu____12366 =
                                                let uu____12375 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12375 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12424  ->
                                                   fun uu____12425  ->
                                                     fun uu____12426  ->
                                                       match (uu____12424,
                                                               uu____12425,
                                                               uu____12426)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12476),
                                                          (a2,uu____12478))
                                                           ->
                                                           let uu____12515 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12515
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12338
                                                uu____12366
                                               in
                                            match uu____12331 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___377_12541 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___377_12541.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___377_12541.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___377_12541.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12553 =
                                                  solve env1 wl'  in
                                                (match uu____12553 with
                                                 | Success (uu____12556,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___378_12560
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___378_12560.attempting);
                                                            wl_deferred =
                                                              (uu___378_12560.wl_deferred);
                                                            ctr =
                                                              (uu___378_12560.ctr);
                                                            defer_ok =
                                                              (uu___378_12560.defer_ok);
                                                            smt_ok =
                                                              (uu___378_12560.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___378_12560.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___378_12560.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12561 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12594 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12594 with
                                | (t1_base,p1_opt) ->
                                    let uu____12630 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12630 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12729 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12729
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
                                               let uu____12782 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12782
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
                                               let uu____12814 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12814
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
                                               let uu____12846 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12846
                                           | uu____12849 -> t_base  in
                                         let uu____12866 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____12866 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12880 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____12880, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____12887 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____12887 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____12923 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____12923 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____12959 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____12959
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
                              let uu____12983 = combine t11 t21 wl2  in
                              (match uu____12983 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13016 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13016
                                     then
                                       let uu____13021 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13021
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13063 ts1 =
               match uu____13063 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13126 = pairwise out t wl2  in
                        (match uu____13126 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13162 =
               let uu____13173 = FStar_List.hd ts  in (uu____13173, [], wl1)
                in
             let uu____13182 = FStar_List.tl ts  in
             aux uu____13162 uu____13182  in
           let uu____13189 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13189 with
           | (this_flex,this_rigid) ->
               let uu____13215 =
                 let uu____13216 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13216.FStar_Syntax_Syntax.n  in
               (match uu____13215 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13241 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13241
                    then
                      let uu____13244 = destruct_flex_t this_flex wl  in
                      (match uu____13244 with
                       | (flex,wl1) ->
                           let uu____13251 = quasi_pattern env flex  in
                           (match uu____13251 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13270 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13270
                                  then
                                    let uu____13275 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13275
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13282 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___379_13285 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___379_13285.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___379_13285.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___379_13285.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___379_13285.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___379_13285.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___379_13285.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___379_13285.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___379_13285.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___379_13285.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13282)
                | uu____13286 ->
                    ((let uu____13288 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13288
                      then
                        let uu____13293 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13293
                      else ());
                     (let uu____13298 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13298 with
                      | (u,_args) ->
                          let uu____13341 =
                            let uu____13342 = FStar_Syntax_Subst.compress u
                               in
                            uu____13342.FStar_Syntax_Syntax.n  in
                          (match uu____13341 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13370 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13370 with
                                 | (u',uu____13389) ->
                                     let uu____13414 =
                                       let uu____13415 = whnf env u'  in
                                       uu____13415.FStar_Syntax_Syntax.n  in
                                     (match uu____13414 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13437 -> false)
                                  in
                               let uu____13439 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___349_13462  ->
                                         match uu___349_13462 with
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
                                              | uu____13476 -> false)
                                         | uu____13480 -> false))
                                  in
                               (match uu____13439 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13495 = whnf env this_rigid
                                         in
                                      let uu____13496 =
                                        FStar_List.collect
                                          (fun uu___350_13502  ->
                                             match uu___350_13502 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13508 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13508]
                                             | uu____13512 -> [])
                                          bounds_probs
                                         in
                                      uu____13495 :: uu____13496  in
                                    let uu____13513 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13513 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13546 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13561 =
                                               let uu____13562 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13562.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13561 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13574 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13574)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13585 -> bound  in
                                           let uu____13586 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13586)  in
                                         (match uu____13546 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13621 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13621
                                                then
                                                  let wl'1 =
                                                    let uu___380_13627 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___380_13627.wl_deferred);
                                                      ctr =
                                                        (uu___380_13627.ctr);
                                                      defer_ok =
                                                        (uu___380_13627.defer_ok);
                                                      smt_ok =
                                                        (uu___380_13627.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___380_13627.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___380_13627.tcenv);
                                                      wl_implicits =
                                                        (uu___380_13627.wl_implicits)
                                                    }  in
                                                  let uu____13628 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13628
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13634 =
                                                  solve_t env eq_prob
                                                    (let uu___381_13636 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___381_13636.wl_deferred);
                                                       ctr =
                                                         (uu___381_13636.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___381_13636.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___381_13636.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___381_13636.tcenv);
                                                       wl_implicits =
                                                         (uu___381_13636.wl_implicits)
                                                     })
                                                   in
                                                match uu____13634 with
                                                | Success uu____13638 ->
                                                    let wl2 =
                                                      let uu___382_13644 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___382_13644.wl_deferred);
                                                        ctr =
                                                          (uu___382_13644.ctr);
                                                        defer_ok =
                                                          (uu___382_13644.defer_ok);
                                                        smt_ok =
                                                          (uu___382_13644.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___382_13644.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___382_13644.tcenv);
                                                        wl_implicits =
                                                          (uu___382_13644.wl_implicits)
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
                                                    let wl3 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl2
                                                       in
                                                    let uu____13660 =
                                                      FStar_List.fold_left
                                                        (fun wl4  ->
                                                           fun p  ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl4) wl3
                                                        bounds_probs
                                                       in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl3)
                                                | Failed (p,msg) ->
                                                    ((let uu____13674 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13674
                                                      then
                                                        let uu____13679 =
                                                          let uu____13681 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13681
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13679
                                                      else ());
                                                     (let uu____13694 =
                                                        let uu____13709 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13709)
                                                         in
                                                      match uu____13694 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13731))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13757 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13757
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
                                                                  let uu____13777
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13777))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13802 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13802
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
                                                                    let uu____13822
                                                                    =
                                                                    let uu____13827
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13827
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13822
                                                                    [] wl2
                                                                     in
                                                                  let uu____13833
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13833))))
                                                      | uu____13834 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____13850 when flip ->
                               let uu____13851 =
                                 let uu____13853 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13855 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13853 uu____13855
                                  in
                               failwith uu____13851
                           | uu____13858 ->
                               let uu____13859 =
                                 let uu____13861 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____13863 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13861 uu____13863
                                  in
                               failwith uu____13859)))))

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
                      (fun uu____13899  ->
                         match uu____13899 with
                         | (x,i) ->
                             let uu____13918 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____13918, i)) bs_lhs
                     in
                  let uu____13921 = lhs  in
                  match uu____13921 with
                  | (uu____13922,u_lhs,uu____13924) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14021 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14031 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14031, univ)
                             in
                          match uu____14021 with
                          | (k,univ) ->
                              let uu____14038 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14038 with
                               | (uu____14055,u,wl3) ->
                                   let uu____14058 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14058, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14084 =
                              let uu____14097 =
                                let uu____14108 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14108 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14159  ->
                                   fun uu____14160  ->
                                     match (uu____14159, uu____14160) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14261 =
                                           let uu____14268 =
                                             let uu____14271 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14271
                                              in
                                           copy_uvar u_lhs [] uu____14268 wl2
                                            in
                                         (match uu____14261 with
                                          | (uu____14300,t_a,wl3) ->
                                              let uu____14303 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14303 with
                                               | (uu____14322,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14097
                                ([], wl1)
                               in
                            (match uu____14084 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___383_14378 = ct  in
                                   let uu____14379 =
                                     let uu____14382 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14382
                                      in
                                   let uu____14397 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___383_14378.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___383_14378.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14379;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14397;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___383_14378.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___384_14415 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___384_14415.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___384_14415.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14418 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14418 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14480 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14480 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14491 =
                                          let uu____14496 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14496)  in
                                        TERM uu____14491  in
                                      let uu____14497 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14497 with
                                       | (sub_prob,wl3) ->
                                           let uu____14511 =
                                             let uu____14512 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14512
                                              in
                                           solve env uu____14511))
                             | (x,imp)::formals2 ->
                                 let uu____14534 =
                                   let uu____14541 =
                                     let uu____14544 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14544
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14541 wl1
                                    in
                                 (match uu____14534 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14565 =
                                          let uu____14568 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14568
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14565 u_x
                                         in
                                      let uu____14569 =
                                        let uu____14572 =
                                          let uu____14575 =
                                            let uu____14576 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14576, imp)  in
                                          [uu____14575]  in
                                        FStar_List.append bs_terms
                                          uu____14572
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14569 formals2 wl2)
                              in
                           let uu____14603 = occurs_check u_lhs arrow1  in
                           (match uu____14603 with
                            | (uu____14616,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14632 =
                                    let uu____14634 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____14634
                                     in
                                  giveup_or_defer env orig wl uu____14632
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
                     (FStar_TypeChecker_Common.prob,worklist)
                       FStar_Pervasives_Native.tuple2)
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____14667 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14667
               then
                 let uu____14672 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14675 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14672 (rel_to_string (p_rel orig)) uu____14675
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____14802 = rhs wl1 scope env1 subst1  in
                     (match uu____14802 with
                      | (rhs_prob,wl2) ->
                          ((let uu____14823 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14823
                            then
                              let uu____14828 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14828
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____14906 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____14906 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___385_14908 = hd1  in
                       let uu____14909 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___385_14908.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___385_14908.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14909
                       }  in
                     let hd21 =
                       let uu___386_14913 = hd2  in
                       let uu____14914 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___386_14913.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___386_14913.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14914
                       }  in
                     let uu____14917 =
                       let uu____14922 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14922
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____14917 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____14943 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____14943
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____14950 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____14950 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15017 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15017
                                  in
                               ((let uu____15035 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15035
                                 then
                                   let uu____15040 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15042 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15040
                                     uu____15042
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15075 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15111 = aux wl [] env [] bs1 bs2  in
               match uu____15111 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15166 = attempt sub_probs wl2  in
                   solve env uu____15166)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist ->
             (FStar_TypeChecker_Common.prob,Prims.string)
               FStar_Pervasives_Native.tuple2 -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___387_15187 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___387_15187.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___387_15187.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15200 = try_solve env wl'  in
          match uu____15200 with
          | Success (uu____15201,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___388_15205 = wl  in
                  {
                    attempting = (uu___388_15205.attempting);
                    wl_deferred = (uu___388_15205.wl_deferred);
                    ctr = (uu___388_15205.ctr);
                    defer_ok = (uu___388_15205.defer_ok);
                    smt_ok = (uu___388_15205.smt_ok);
                    umax_heuristic_ok = (uu___388_15205.umax_heuristic_ok);
                    tcenv = (uu___388_15205.tcenv);
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
        (let uu____15217 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15217 wl)

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
              let uu____15231 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15231 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15265 = lhs1  in
              match uu____15265 with
              | (uu____15268,ctx_u,uu____15270) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15278 ->
                        let uu____15279 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15279 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15328 = quasi_pattern env1 lhs1  in
              match uu____15328 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15362) ->
                  let uu____15367 = lhs1  in
                  (match uu____15367 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15382 = occurs_check ctx_u rhs1  in
                       (match uu____15382 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15433 =
                                let uu____15441 =
                                  let uu____15443 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15443
                                   in
                                FStar_Util.Inl uu____15441  in
                              (uu____15433, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15471 =
                                 let uu____15473 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15473  in
                               if uu____15471
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15500 =
                                    let uu____15508 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15508  in
                                  let uu____15514 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15500, uu____15514)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15558 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15558 with
              | (rhs_hd,args) ->
                  let uu____15601 = FStar_Util.prefix args  in
                  (match uu____15601 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15673 = lhs1  in
                       (match uu____15673 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15677 =
                              let uu____15688 =
                                let uu____15695 =
                                  let uu____15698 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15698
                                   in
                                copy_uvar u_lhs [] uu____15695 wl1  in
                              match uu____15688 with
                              | (uu____15725,t_last_arg,wl2) ->
                                  let uu____15728 =
                                    let uu____15735 =
                                      let uu____15736 =
                                        let uu____15745 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15745]  in
                                      FStar_List.append bs_lhs uu____15736
                                       in
                                    copy_uvar u_lhs uu____15735 t_res_lhs wl2
                                     in
                                  (match uu____15728 with
                                   | (uu____15780,lhs',wl3) ->
                                       let uu____15783 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15783 with
                                        | (uu____15800,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15677 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____15821 =
                                     let uu____15822 =
                                       let uu____15827 =
                                         let uu____15828 =
                                           let uu____15831 =
                                             let uu____15836 =
                                               let uu____15837 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____15837]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____15836
                                              in
                                           uu____15831
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____15828
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____15827)  in
                                     TERM uu____15822  in
                                   [uu____15821]  in
                                 let uu____15864 =
                                   let uu____15871 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____15871 with
                                   | (p1,wl3) ->
                                       let uu____15891 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____15891 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____15864 with
                                  | (sub_probs,wl3) ->
                                      let uu____15923 =
                                        let uu____15924 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____15924  in
                                      solve env1 uu____15923))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____15958 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____15958 with
                | (uu____15976,args) ->
                    (match args with | [] -> false | uu____16012 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16031 =
                  let uu____16032 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16032.FStar_Syntax_Syntax.n  in
                match uu____16031 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16036 -> true
                | uu____16052 -> false  in
              let uu____16054 = quasi_pattern env1 lhs1  in
              match uu____16054 with
              | FStar_Pervasives_Native.None  ->
                  let uu____16065 =
                    let uu____16067 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____16067
                     in
                  giveup_or_defer env1 orig1 wl1 uu____16065
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16076 = is_app rhs1  in
                  if uu____16076
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16081 = is_arrow rhs1  in
                     if uu____16081
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____16086 =
                          let uu____16088 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____16088
                           in
                        giveup_or_defer env1 orig1 wl1 uu____16086))
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
                let uu____16099 = lhs  in
                (match uu____16099 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16103 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16103 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16121 =
                              let uu____16125 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16125
                               in
                            FStar_All.pipe_right uu____16121
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16146 = occurs_check ctx_uv rhs1  in
                          (match uu____16146 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16175 =
                                   let uu____16177 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____16177
                                    in
                                 giveup_or_defer env orig wl uu____16175
                               else
                                 (let uu____16183 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16183
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16190 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16190
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____16194 =
                                         let uu____16196 =
                                           names_to_string1 fvs2  in
                                         let uu____16198 =
                                           names_to_string1 fvs1  in
                                         let uu____16200 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____16196 uu____16198
                                           uu____16200
                                          in
                                       giveup_or_defer env orig wl
                                         uu____16194)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16212 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____16219 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16219 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16245 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16245
                             | (FStar_Util.Inl msg,uu____16247) ->
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
                  (let uu____16292 =
                     let uu____16309 = quasi_pattern env lhs  in
                     let uu____16316 = quasi_pattern env rhs  in
                     (uu____16309, uu____16316)  in
                   match uu____16292 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16359 = lhs  in
                       (match uu____16359 with
                        | ({ FStar_Syntax_Syntax.n = uu____16360;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16362;_},u_lhs,uu____16364)
                            ->
                            let uu____16367 = rhs  in
                            (match uu____16367 with
                             | (uu____16368,u_rhs,uu____16370) ->
                                 let uu____16371 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16371
                                 then
                                   let uu____16378 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16378
                                 else
                                   (let uu____16381 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16381 with
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
                                        let uu____16413 =
                                          let uu____16420 =
                                            let uu____16423 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16423
                                             in
                                          new_uvar
                                            (Prims.strcat "flex-flex quasi:"
                                               (Prims.strcat "\tlhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16420
                                            FStar_Syntax_Syntax.Strict
                                           in
                                        (match uu____16413 with
                                         | (uu____16429,w,wl1) ->
                                             let w_app =
                                               let uu____16435 =
                                                 let uu____16440 =
                                                   FStar_List.map
                                                     (fun uu____16451  ->
                                                        match uu____16451
                                                        with
                                                        | (z,uu____16459) ->
                                                            let uu____16464 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16464) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16440
                                                  in
                                               uu____16435
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16468 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16468
                                               then
                                                 let uu____16473 =
                                                   let uu____16477 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16479 =
                                                     let uu____16483 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16485 =
                                                       let uu____16489 =
                                                         term_to_string w  in
                                                       let uu____16491 =
                                                         let uu____16495 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16504 =
                                                           let uu____16508 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16517 =
                                                             let uu____16521
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16521]
                                                              in
                                                           uu____16508 ::
                                                             uu____16517
                                                            in
                                                         uu____16495 ::
                                                           uu____16504
                                                          in
                                                       uu____16489 ::
                                                         uu____16491
                                                        in
                                                     uu____16483 ::
                                                       uu____16485
                                                      in
                                                   uu____16477 :: uu____16479
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16473
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16538 =
                                                     let uu____16543 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16543)  in
                                                   TERM uu____16538  in
                                                 let uu____16544 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16544
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16552 =
                                                        let uu____16557 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16557)
                                                         in
                                                      TERM uu____16552  in
                                                    [s1; s2])
                                                  in
                                               let uu____16558 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16558))))))
                   | uu____16559 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16630 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16630
            then
              let uu____16635 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16637 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16639 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16641 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16635 uu____16637 uu____16639 uu____16641
            else ());
           (let uu____16652 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16652 with
            | (head1,args1) ->
                let uu____16695 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16695 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16765 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____16765 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16795 =
                         let uu____16797 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____16799 = args_to_string args1  in
                         let uu____16803 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____16805 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____16797 uu____16799 uu____16803 uu____16805
                          in
                       giveup env1 uu____16795 orig
                     else
                       (let uu____16812 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____16821 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____16821 = FStar_Syntax_Util.Equal)
                           in
                        if uu____16812
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___389_16825 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___389_16825.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___389_16825.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___389_16825.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___389_16825.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___389_16825.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___389_16825.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___389_16825.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___389_16825.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____16835 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____16835
                                    else solve env1 wl2))
                        else
                          (let uu____16840 = base_and_refinement env1 t1  in
                           match uu____16840 with
                           | (base1,refinement1) ->
                               let uu____16865 = base_and_refinement env1 t2
                                  in
                               (match uu____16865 with
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
                                           let uu____17030 =
                                             FStar_List.fold_right
                                               (fun uu____17070  ->
                                                  fun uu____17071  ->
                                                    match (uu____17070,
                                                            uu____17071)
                                                    with
                                                    | (((a1,uu____17123),
                                                        (a2,uu____17125)),
                                                       (probs,wl3)) ->
                                                        let uu____17174 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17174
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17030 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17217 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17217
                                                 then
                                                   let uu____17222 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17222
                                                 else ());
                                                (let uu____17228 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17228
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
                                                    (let uu____17255 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17255 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17271 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17271
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17279 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17279))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17303 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17303 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17317 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17317)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17343 =
                                           match uu____17343 with
                                           | (prob,reason) ->
                                               ((let uu____17354 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17354
                                                 then
                                                   let uu____17359 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17361 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17359 uu____17361
                                                     reason
                                                 else ());
                                                (let uu____17366 =
                                                   let uu____17375 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17378 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17375, uu____17378)
                                                    in
                                                 match uu____17366 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17391 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17391 with
                                                      | (head1',uu____17409)
                                                          ->
                                                          let uu____17434 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17434
                                                           with
                                                           | (head2',uu____17452)
                                                               ->
                                                               let uu____17477
                                                                 =
                                                                 let uu____17482
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17483
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17482,
                                                                   uu____17483)
                                                                  in
                                                               (match uu____17477
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17485
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17485
                                                                    then
                                                                    let uu____17490
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17492
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17494
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17496
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17490
                                                                    uu____17492
                                                                    uu____17494
                                                                    uu____17496
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17501
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___390_17509
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___390_17509.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17511
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17511
                                                                    then
                                                                    let uu____17516
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17516
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17521 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17533 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17533 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17541 =
                                             let uu____17542 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17542.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17541 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17547 -> false  in
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
                                          | uu____17550 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17553 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___391_17589 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___391_17589.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___391_17589.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___391_17589.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___391_17589.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___391_17589.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___391_17589.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___391_17589.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___391_17589.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17665 = destruct_flex_t scrutinee wl1  in
             match uu____17665 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17676 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17676 with
                  | (xs,pat_term,uu____17692,uu____17693) ->
                      let uu____17698 =
                        FStar_List.fold_left
                          (fun uu____17721  ->
                             fun x  ->
                               match uu____17721 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17742 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17742 with
                                    | (uu____17761,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17698 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____17782 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____17782 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___392_17799 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___392_17799.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___392_17799.umax_heuristic_ok);
                                    tcenv = (uu___392_17799.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____17811 = solve env1 wl'  in
                                (match uu____17811 with
                                 | Success (uu____17814,imps) ->
                                     let wl'1 =
                                       let uu___393_17817 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___393_17817.wl_deferred);
                                         ctr = (uu___393_17817.ctr);
                                         defer_ok = (uu___393_17817.defer_ok);
                                         smt_ok = (uu___393_17817.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___393_17817.umax_heuristic_ok);
                                         tcenv = (uu___393_17817.tcenv);
                                         wl_implicits =
                                           (uu___393_17817.wl_implicits)
                                       }  in
                                     let uu____17818 = solve env1 wl'1  in
                                     (match uu____17818 with
                                      | Success (uu____17821,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___394_17825 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___394_17825.attempting);
                                                 wl_deferred =
                                                   (uu___394_17825.wl_deferred);
                                                 ctr = (uu___394_17825.ctr);
                                                 defer_ok =
                                                   (uu___394_17825.defer_ok);
                                                 smt_ok =
                                                   (uu___394_17825.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___394_17825.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___394_17825.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____17826 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17833 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____17856 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____17856
                 then
                   let uu____17861 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____17863 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17861 uu____17863
                 else ());
                (let uu____17868 =
                   let uu____17889 =
                     let uu____17898 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____17898)  in
                   let uu____17905 =
                     let uu____17914 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____17914)  in
                   (uu____17889, uu____17905)  in
                 match uu____17868 with
                 | ((uu____17944,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____17947;
                                   FStar_Syntax_Syntax.vars = uu____17948;_}),
                    (s,t)) ->
                     let uu____18019 =
                       let uu____18021 = is_flex scrutinee  in
                       Prims.op_Negation uu____18021  in
                     if uu____18019
                     then
                       ((let uu____18032 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18032
                         then
                           let uu____18037 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18037
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18056 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18056
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18071 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18071
                           then
                             let uu____18076 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18078 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18076 uu____18078
                           else ());
                          (let pat_discriminates uu___351_18103 =
                             match uu___351_18103 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18119;
                                  FStar_Syntax_Syntax.p = uu____18120;_},FStar_Pervasives_Native.None
                                ,uu____18121) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18135;
                                  FStar_Syntax_Syntax.p = uu____18136;_},FStar_Pervasives_Native.None
                                ,uu____18137) -> true
                             | uu____18164 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18267 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18267 with
                                       | (uu____18269,uu____18270,t') ->
                                           let uu____18288 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18288 with
                                            | (FullMatch ,uu____18300) ->
                                                true
                                            | (HeadMatch
                                               uu____18314,uu____18315) ->
                                                true
                                            | uu____18330 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18367 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18367
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18378 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18378 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18466,uu____18467) ->
                                       branches1
                                   | uu____18612 -> branches  in
                                 let uu____18667 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18676 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18676 with
                                        | (p,uu____18680,uu____18681) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_8  -> FStar_Util.Inr _0_8)
                                   uu____18667))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18739 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18739 with
                                | (p,uu____18748,e) ->
                                    ((let uu____18767 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____18767
                                      then
                                        let uu____18772 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____18774 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18772 uu____18774
                                      else ());
                                     (let uu____18779 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_9  -> FStar_Util.Inr _0_9)
                                        uu____18779)))))
                 | ((s,t),(uu____18796,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____18799;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18800;_}))
                     ->
                     let uu____18869 =
                       let uu____18871 = is_flex scrutinee  in
                       Prims.op_Negation uu____18871  in
                     if uu____18869
                     then
                       ((let uu____18882 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18882
                         then
                           let uu____18887 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18887
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18906 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18906
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18921 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18921
                           then
                             let uu____18926 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18928 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18926 uu____18928
                           else ());
                          (let pat_discriminates uu___351_18953 =
                             match uu___351_18953 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18969;
                                  FStar_Syntax_Syntax.p = uu____18970;_},FStar_Pervasives_Native.None
                                ,uu____18971) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18985;
                                  FStar_Syntax_Syntax.p = uu____18986;_},FStar_Pervasives_Native.None
                                ,uu____18987) -> true
                             | uu____19014 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19117 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19117 with
                                       | (uu____19119,uu____19120,t') ->
                                           let uu____19138 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19138 with
                                            | (FullMatch ,uu____19150) ->
                                                true
                                            | (HeadMatch
                                               uu____19164,uu____19165) ->
                                                true
                                            | uu____19180 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19217 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19217
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19228 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19228 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19316,uu____19317) ->
                                       branches1
                                   | uu____19462 -> branches  in
                                 let uu____19517 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19526 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19526 with
                                        | (p,uu____19530,uu____19531) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_10  -> FStar_Util.Inr _0_10)
                                   uu____19517))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19589 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19589 with
                                | (p,uu____19598,e) ->
                                    ((let uu____19617 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19617
                                      then
                                        let uu____19622 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19624 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19622 uu____19624
                                      else ());
                                     (let uu____19629 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_11  -> FStar_Util.Inr _0_11)
                                        uu____19629)))))
                 | uu____19644 ->
                     ((let uu____19666 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19666
                       then
                         let uu____19671 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19673 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19671 uu____19673
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19719 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19719
            then
              let uu____19724 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19726 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19728 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19730 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19724 uu____19726 uu____19728 uu____19730
            else ());
           (let uu____19735 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19735 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____19766,uu____19767) ->
                     let rec may_relate head3 =
                       let uu____19795 =
                         let uu____19796 = FStar_Syntax_Subst.compress head3
                            in
                         uu____19796.FStar_Syntax_Syntax.n  in
                       match uu____19795 with
                       | FStar_Syntax_Syntax.Tm_name uu____19800 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19802 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19827 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____19827 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19829 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19832
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19833 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____19836,uu____19837) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____19879) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____19885) ->
                           may_relate t
                       | uu____19890 -> false  in
                     let uu____19892 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____19892 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____19913 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____19913
                          then
                            let uu____19916 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____19916 with
                             | (guard,wl2) ->
                                 let uu____19923 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____19923)
                          else
                            (let uu____19926 =
                               let uu____19928 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____19930 =
                                 let uu____19932 =
                                   let uu____19936 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____19936
                                     (fun x  ->
                                        let uu____19943 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____19943)
                                    in
                                 FStar_Util.dflt "" uu____19932  in
                               let uu____19948 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____19950 =
                                 let uu____19952 =
                                   let uu____19956 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____19956
                                     (fun x  ->
                                        let uu____19963 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____19963)
                                    in
                                 FStar_Util.dflt "" uu____19952  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____19928 uu____19930 uu____19948
                                 uu____19950
                                in
                             giveup env1 uu____19926 orig))
                 | (HeadMatch (true ),uu____19969) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____19984 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____19984 with
                        | (guard,wl2) ->
                            let uu____19991 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____19991)
                     else
                       (let uu____19994 =
                          let uu____19996 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____19998 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____19996 uu____19998
                           in
                        giveup env1 uu____19994 orig)
                 | (uu____20001,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___395_20015 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___395_20015.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___395_20015.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___395_20015.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___395_20015.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___395_20015.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___395_20015.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___395_20015.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___395_20015.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20042 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20042
          then
            let uu____20045 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20045
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20051 =
                let uu____20054 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20054  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20051 t1);
             (let uu____20073 =
                let uu____20076 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20076  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20073 t2);
             (let uu____20095 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20095
              then
                let uu____20099 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20101 =
                  let uu____20103 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20105 =
                    let uu____20107 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____20107  in
                  Prims.strcat uu____20103 uu____20105  in
                let uu____20110 =
                  let uu____20112 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20114 =
                    let uu____20116 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____20116  in
                  Prims.strcat uu____20112 uu____20114  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20099 uu____20101 uu____20110
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20123,uu____20124) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20148,FStar_Syntax_Syntax.Tm_delayed uu____20149) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20173,uu____20174) ->
                  let uu____20201 =
                    let uu___396_20202 = problem  in
                    let uu____20203 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___396_20202.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20203;
                      FStar_TypeChecker_Common.relation =
                        (uu___396_20202.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___396_20202.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___396_20202.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___396_20202.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___396_20202.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___396_20202.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___396_20202.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___396_20202.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20201 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20204,uu____20205) ->
                  let uu____20212 =
                    let uu___397_20213 = problem  in
                    let uu____20214 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___397_20213.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20214;
                      FStar_TypeChecker_Common.relation =
                        (uu___397_20213.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___397_20213.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___397_20213.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___397_20213.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___397_20213.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___397_20213.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___397_20213.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___397_20213.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20212 wl
              | (uu____20215,FStar_Syntax_Syntax.Tm_ascribed uu____20216) ->
                  let uu____20243 =
                    let uu___398_20244 = problem  in
                    let uu____20245 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___398_20244.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___398_20244.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___398_20244.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20245;
                      FStar_TypeChecker_Common.element =
                        (uu___398_20244.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___398_20244.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___398_20244.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___398_20244.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___398_20244.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___398_20244.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20243 wl
              | (uu____20246,FStar_Syntax_Syntax.Tm_meta uu____20247) ->
                  let uu____20254 =
                    let uu___399_20255 = problem  in
                    let uu____20256 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___399_20255.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___399_20255.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___399_20255.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20256;
                      FStar_TypeChecker_Common.element =
                        (uu___399_20255.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___399_20255.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___399_20255.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___399_20255.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___399_20255.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___399_20255.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20254 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20258),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20260)) ->
                  let uu____20269 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20269
              | (FStar_Syntax_Syntax.Tm_bvar uu____20270,uu____20271) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20273,FStar_Syntax_Syntax.Tm_bvar uu____20274) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___352_20344 =
                    match uu___352_20344 with
                    | [] -> c
                    | bs ->
                        let uu____20372 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20372
                     in
                  let uu____20383 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20383 with
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
                                    let uu____20532 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20532
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
                  let mk_t t l uu___353_20621 =
                    match uu___353_20621 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20663 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20663 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____20808 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____20809 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____20808
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____20809 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____20811,uu____20812) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20843 -> true
                    | uu____20863 -> false  in
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
                      (let uu____20923 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___400_20931 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___400_20931.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___400_20931.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___400_20931.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___400_20931.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___400_20931.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___400_20931.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___400_20931.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___400_20931.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___400_20931.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___400_20931.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___400_20931.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___400_20931.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___400_20931.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___400_20931.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___400_20931.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___400_20931.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___400_20931.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___400_20931.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___400_20931.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___400_20931.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___400_20931.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___400_20931.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___400_20931.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___400_20931.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___400_20931.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___400_20931.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___400_20931.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___400_20931.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___400_20931.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___400_20931.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___400_20931.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___400_20931.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___400_20931.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___400_20931.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___400_20931.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___400_20931.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___400_20931.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___400_20931.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___400_20931.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___400_20931.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____20923 with
                       | (uu____20936,ty,uu____20938) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____20947 =
                                 let uu____20948 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____20948.FStar_Syntax_Syntax.n  in
                               match uu____20947 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20951 ->
                                   let uu____20958 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____20958
                               | uu____20959 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____20962 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____20962
                             then
                               let uu____20967 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____20969 =
                                 let uu____20971 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20971
                                  in
                               let uu____20972 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20967 uu____20969 uu____20972
                             else ());
                            r1))
                     in
                  let uu____20977 =
                    let uu____20994 = maybe_eta t1  in
                    let uu____21001 = maybe_eta t2  in
                    (uu____20994, uu____21001)  in
                  (match uu____20977 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___401_21043 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___401_21043.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___401_21043.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___401_21043.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___401_21043.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___401_21043.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___401_21043.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___401_21043.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___401_21043.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21064 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21064
                       then
                         let uu____21067 = destruct_flex_t not_abs wl  in
                         (match uu____21067 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21084 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21084.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21084.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21084.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21084.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21084.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21084.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21084.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21084.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21108 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21108
                       then
                         let uu____21111 = destruct_flex_t not_abs wl  in
                         (match uu____21111 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21128 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21128.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21128.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21128.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21128.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21128.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21128.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21128.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21128.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21132 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21150,FStar_Syntax_Syntax.Tm_abs uu____21151) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21182 -> true
                    | uu____21202 -> false  in
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
                      (let uu____21262 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___400_21270 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___400_21270.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___400_21270.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___400_21270.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___400_21270.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___400_21270.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___400_21270.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___400_21270.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___400_21270.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___400_21270.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___400_21270.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___400_21270.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___400_21270.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___400_21270.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___400_21270.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___400_21270.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___400_21270.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___400_21270.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___400_21270.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___400_21270.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___400_21270.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___400_21270.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___400_21270.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___400_21270.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___400_21270.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___400_21270.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___400_21270.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___400_21270.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___400_21270.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___400_21270.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___400_21270.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___400_21270.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___400_21270.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___400_21270.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___400_21270.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___400_21270.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___400_21270.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___400_21270.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___400_21270.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___400_21270.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___400_21270.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____21262 with
                       | (uu____21275,ty,uu____21277) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21286 =
                                 let uu____21287 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21287.FStar_Syntax_Syntax.n  in
                               match uu____21286 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21290 ->
                                   let uu____21297 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21297
                               | uu____21298 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21301 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21301
                             then
                               let uu____21306 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21308 =
                                 let uu____21310 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21310
                                  in
                               let uu____21311 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21306 uu____21308 uu____21311
                             else ());
                            r1))
                     in
                  let uu____21316 =
                    let uu____21333 = maybe_eta t1  in
                    let uu____21340 = maybe_eta t2  in
                    (uu____21333, uu____21340)  in
                  (match uu____21316 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___401_21382 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___401_21382.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___401_21382.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___401_21382.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___401_21382.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___401_21382.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___401_21382.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___401_21382.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___401_21382.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21403 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21403
                       then
                         let uu____21406 = destruct_flex_t not_abs wl  in
                         (match uu____21406 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21423 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21423.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21423.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21423.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21423.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21423.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21423.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21423.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21423.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21447 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21447
                       then
                         let uu____21450 = destruct_flex_t not_abs wl  in
                         (match uu____21450 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___402_21467 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___402_21467.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___402_21467.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___402_21467.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___402_21467.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___402_21467.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___402_21467.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___402_21467.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___402_21467.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____21471 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21501 =
                    let uu____21506 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21506 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___403_21534 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___403_21534.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___403_21534.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___404_21536 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___404_21536.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___404_21536.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21537,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___403_21552 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___403_21552.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___403_21552.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___404_21554 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___404_21554.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___404_21554.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21555 -> (x1, x2)  in
                  (match uu____21501 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21574 = as_refinement false env t11  in
                       (match uu____21574 with
                        | (x12,phi11) ->
                            let uu____21582 = as_refinement false env t21  in
                            (match uu____21582 with
                             | (x22,phi21) ->
                                 ((let uu____21591 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21591
                                   then
                                     ((let uu____21596 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21598 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21600 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21596
                                         uu____21598 uu____21600);
                                      (let uu____21603 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21605 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21607 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21603
                                         uu____21605 uu____21607))
                                   else ());
                                  (let uu____21612 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21612 with
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
                                         let uu____21683 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21683
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21695 =
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
                                         (let uu____21708 =
                                            let uu____21711 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21711
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21708
                                            (p_guard base_prob));
                                         (let uu____21730 =
                                            let uu____21733 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21733
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21730
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____21752 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____21752)
                                          in
                                       let has_uvars =
                                         (let uu____21757 =
                                            let uu____21759 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____21759
                                             in
                                          Prims.op_Negation uu____21757) ||
                                           (let uu____21763 =
                                              let uu____21765 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____21765
                                               in
                                            Prims.op_Negation uu____21763)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____21769 =
                                           let uu____21774 =
                                             let uu____21783 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____21783]  in
                                           mk_t_problem wl1 uu____21774 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____21769 with
                                          | (ref_prob,wl2) ->
                                              let uu____21805 =
                                                solve env1
                                                  (let uu___405_21807 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___405_21807.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___405_21807.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___405_21807.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___405_21807.tcenv);
                                                     wl_implicits =
                                                       (uu___405_21807.wl_implicits)
                                                   })
                                                 in
                                              (match uu____21805 with
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
                                               | Success uu____21824 ->
                                                   let guard =
                                                     let uu____21832 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____21832
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___406_21841 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___406_21841.attempting);
                                                       wl_deferred =
                                                         (uu___406_21841.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___406_21841.defer_ok);
                                                       smt_ok =
                                                         (uu___406_21841.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___406_21841.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___406_21841.tcenv);
                                                       wl_implicits =
                                                         (uu___406_21841.wl_implicits)
                                                     }  in
                                                   let uu____21843 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____21843))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____21846,FStar_Syntax_Syntax.Tm_uvar uu____21847) ->
                  let uu____21872 = destruct_flex_t t1 wl  in
                  (match uu____21872 with
                   | (f1,wl1) ->
                       let uu____21879 = destruct_flex_t t2 wl1  in
                       (match uu____21879 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21886;
                    FStar_Syntax_Syntax.pos = uu____21887;
                    FStar_Syntax_Syntax.vars = uu____21888;_},uu____21889),FStar_Syntax_Syntax.Tm_uvar
                 uu____21890) ->
                  let uu____21939 = destruct_flex_t t1 wl  in
                  (match uu____21939 with
                   | (f1,wl1) ->
                       let uu____21946 = destruct_flex_t t2 wl1  in
                       (match uu____21946 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____21953,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21954;
                    FStar_Syntax_Syntax.pos = uu____21955;
                    FStar_Syntax_Syntax.vars = uu____21956;_},uu____21957))
                  ->
                  let uu____22006 = destruct_flex_t t1 wl  in
                  (match uu____22006 with
                   | (f1,wl1) ->
                       let uu____22013 = destruct_flex_t t2 wl1  in
                       (match uu____22013 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22020;
                    FStar_Syntax_Syntax.pos = uu____22021;
                    FStar_Syntax_Syntax.vars = uu____22022;_},uu____22023),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22024;
                    FStar_Syntax_Syntax.pos = uu____22025;
                    FStar_Syntax_Syntax.vars = uu____22026;_},uu____22027))
                  ->
                  let uu____22100 = destruct_flex_t t1 wl  in
                  (match uu____22100 with
                   | (f1,wl1) ->
                       let uu____22107 = destruct_flex_t t2 wl1  in
                       (match uu____22107 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22114,uu____22115) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22128 = destruct_flex_t t1 wl  in
                  (match uu____22128 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22135;
                    FStar_Syntax_Syntax.pos = uu____22136;
                    FStar_Syntax_Syntax.vars = uu____22137;_},uu____22138),uu____22139)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22176 = destruct_flex_t t1 wl  in
                  (match uu____22176 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22183,FStar_Syntax_Syntax.Tm_uvar uu____22184) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22197,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22198;
                    FStar_Syntax_Syntax.pos = uu____22199;
                    FStar_Syntax_Syntax.vars = uu____22200;_},uu____22201))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22238,FStar_Syntax_Syntax.Tm_arrow uu____22239) ->
                  solve_t' env
                    (let uu___407_22267 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___407_22267.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___407_22267.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___407_22267.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___407_22267.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___407_22267.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___407_22267.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___407_22267.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___407_22267.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___407_22267.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22268;
                    FStar_Syntax_Syntax.pos = uu____22269;
                    FStar_Syntax_Syntax.vars = uu____22270;_},uu____22271),FStar_Syntax_Syntax.Tm_arrow
                 uu____22272) ->
                  solve_t' env
                    (let uu___407_22324 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___407_22324.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___407_22324.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___407_22324.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___407_22324.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___407_22324.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___407_22324.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___407_22324.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___407_22324.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___407_22324.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22325,FStar_Syntax_Syntax.Tm_uvar uu____22326) ->
                  let uu____22339 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22339
              | (uu____22340,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22341;
                    FStar_Syntax_Syntax.pos = uu____22342;
                    FStar_Syntax_Syntax.vars = uu____22343;_},uu____22344))
                  ->
                  let uu____22381 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22381
              | (FStar_Syntax_Syntax.Tm_uvar uu____22382,uu____22383) ->
                  let uu____22396 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22396
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22397;
                    FStar_Syntax_Syntax.pos = uu____22398;
                    FStar_Syntax_Syntax.vars = uu____22399;_},uu____22400),uu____22401)
                  ->
                  let uu____22438 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22438
              | (FStar_Syntax_Syntax.Tm_refine uu____22439,uu____22440) ->
                  let t21 =
                    let uu____22448 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22448  in
                  solve_t env
                    (let uu___408_22474 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___408_22474.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___408_22474.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___408_22474.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___408_22474.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___408_22474.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___408_22474.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___408_22474.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___408_22474.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___408_22474.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22475,FStar_Syntax_Syntax.Tm_refine uu____22476) ->
                  let t11 =
                    let uu____22484 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22484  in
                  solve_t env
                    (let uu___409_22510 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___409_22510.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___409_22510.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___409_22510.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___409_22510.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___409_22510.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___409_22510.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___409_22510.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___409_22510.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___409_22510.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22592 =
                    let uu____22593 = guard_of_prob env wl problem t1 t2  in
                    match uu____22593 with
                    | (guard,wl1) ->
                        let uu____22600 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22600
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____22819 = br1  in
                        (match uu____22819 with
                         | (p1,w1,uu____22848) ->
                             let uu____22865 = br2  in
                             (match uu____22865 with
                              | (p2,w2,uu____22888) ->
                                  let uu____22893 =
                                    let uu____22895 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____22895  in
                                  if uu____22893
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____22922 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____22922 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____22959 = br2  in
                                         (match uu____22959 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____22992 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____22992
                                                 in
                                              let uu____22997 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23028,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23049) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23108 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23108 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____22997
                                                (fun uu____23180  ->
                                                   match uu____23180 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23217 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23217
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23238
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23238
                                                              then
                                                                let uu____23243
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23245
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23243
                                                                  uu____23245
                                                              else ());
                                                             (let uu____23251
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23251
                                                                (fun
                                                                   uu____23287
                                                                    ->
                                                                   match uu____23287
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
                    | uu____23416 -> FStar_Pervasives_Native.None  in
                  let uu____23457 = solve_branches wl brs1 brs2  in
                  (match uu____23457 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23508 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23508 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23542 =
                                FStar_List.map
                                  (fun uu____23554  ->
                                     match uu____23554 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23542  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23563 =
                              let uu____23564 =
                                let uu____23565 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23565
                                  (let uu___410_23573 = wl3  in
                                   {
                                     attempting = (uu___410_23573.attempting);
                                     wl_deferred =
                                       (uu___410_23573.wl_deferred);
                                     ctr = (uu___410_23573.ctr);
                                     defer_ok = (uu___410_23573.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___410_23573.umax_heuristic_ok);
                                     tcenv = (uu___410_23573.tcenv);
                                     wl_implicits =
                                       (uu___410_23573.wl_implicits)
                                   })
                                 in
                              solve env uu____23564  in
                            (match uu____23563 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23578 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23585,uu____23586) ->
                  let head1 =
                    let uu____23610 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23610
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23656 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23656
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23702 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23702
                    then
                      let uu____23706 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23708 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23710 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23706 uu____23708 uu____23710
                    else ());
                   (let no_free_uvars t =
                      (let uu____23724 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23724) &&
                        (let uu____23728 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23728)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23745 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23745 = FStar_Syntax_Util.Equal  in
                    let uu____23746 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23746
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23750 = equal t1 t2  in
                         (if uu____23750
                          then
                            let uu____23753 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23753
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23758 =
                            let uu____23765 = equal t1 t2  in
                            if uu____23765
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23778 = mk_eq2 wl env orig t1 t2  in
                               match uu____23778 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23758 with
                          | (guard,wl1) ->
                              let uu____23799 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23799))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____23802,uu____23803) ->
                  let head1 =
                    let uu____23811 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23811
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23857 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23857
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23903 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23903
                    then
                      let uu____23907 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23909 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23911 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23907 uu____23909 uu____23911
                    else ());
                   (let no_free_uvars t =
                      (let uu____23925 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23925) &&
                        (let uu____23929 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23929)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23946 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23946 = FStar_Syntax_Util.Equal  in
                    let uu____23947 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23947
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23951 = equal t1 t2  in
                         (if uu____23951
                          then
                            let uu____23954 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23954
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23959 =
                            let uu____23966 = equal t1 t2  in
                            if uu____23966
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23979 = mk_eq2 wl env orig t1 t2  in
                               match uu____23979 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23959 with
                          | (guard,wl1) ->
                              let uu____24000 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24000))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24003,uu____24004) ->
                  let head1 =
                    let uu____24006 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24006
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24052 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24052
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24098 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24098
                    then
                      let uu____24102 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24104 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24106 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24102 uu____24104 uu____24106
                    else ());
                   (let no_free_uvars t =
                      (let uu____24120 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24120) &&
                        (let uu____24124 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24124)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24141 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24141 = FStar_Syntax_Util.Equal  in
                    let uu____24142 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24142
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24146 = equal t1 t2  in
                         (if uu____24146
                          then
                            let uu____24149 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24149
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24154 =
                            let uu____24161 = equal t1 t2  in
                            if uu____24161
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24174 = mk_eq2 wl env orig t1 t2  in
                               match uu____24174 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24154 with
                          | (guard,wl1) ->
                              let uu____24195 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24195))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24198,uu____24199) ->
                  let head1 =
                    let uu____24201 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24201
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24247 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24247
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24293 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24293
                    then
                      let uu____24297 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24299 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24301 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24297 uu____24299 uu____24301
                    else ());
                   (let no_free_uvars t =
                      (let uu____24315 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24315) &&
                        (let uu____24319 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24319)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24336 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24336 = FStar_Syntax_Util.Equal  in
                    let uu____24337 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24337
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24341 = equal t1 t2  in
                         (if uu____24341
                          then
                            let uu____24344 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24344
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24349 =
                            let uu____24356 = equal t1 t2  in
                            if uu____24356
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24369 = mk_eq2 wl env orig t1 t2  in
                               match uu____24369 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24349 with
                          | (guard,wl1) ->
                              let uu____24390 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24390))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24393,uu____24394) ->
                  let head1 =
                    let uu____24396 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24396
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24442 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24442
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24488 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24488
                    then
                      let uu____24492 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24494 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24496 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24492 uu____24494 uu____24496
                    else ());
                   (let no_free_uvars t =
                      (let uu____24510 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24510) &&
                        (let uu____24514 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24514)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24531 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24531 = FStar_Syntax_Util.Equal  in
                    let uu____24532 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24532
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24536 = equal t1 t2  in
                         (if uu____24536
                          then
                            let uu____24539 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24539
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24544 =
                            let uu____24551 = equal t1 t2  in
                            if uu____24551
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24564 = mk_eq2 wl env orig t1 t2  in
                               match uu____24564 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24544 with
                          | (guard,wl1) ->
                              let uu____24585 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24585))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24588,uu____24589) ->
                  let head1 =
                    let uu____24607 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24607
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24653 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24653
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24699 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24699
                    then
                      let uu____24703 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24705 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24707 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24703 uu____24705 uu____24707
                    else ());
                   (let no_free_uvars t =
                      (let uu____24721 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24721) &&
                        (let uu____24725 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24725)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24742 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24742 = FStar_Syntax_Util.Equal  in
                    let uu____24743 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24743
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24747 = equal t1 t2  in
                         (if uu____24747
                          then
                            let uu____24750 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24750
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24755 =
                            let uu____24762 = equal t1 t2  in
                            if uu____24762
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24775 = mk_eq2 wl env orig t1 t2  in
                               match uu____24775 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24755 with
                          | (guard,wl1) ->
                              let uu____24796 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24796))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24799,FStar_Syntax_Syntax.Tm_match uu____24800) ->
                  let head1 =
                    let uu____24824 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24824
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24870 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24870
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24916 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24916
                    then
                      let uu____24920 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24922 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24924 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24920 uu____24922 uu____24924
                    else ());
                   (let no_free_uvars t =
                      (let uu____24938 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24938) &&
                        (let uu____24942 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24942)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24959 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24959 = FStar_Syntax_Util.Equal  in
                    let uu____24960 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24960
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24964 = equal t1 t2  in
                         (if uu____24964
                          then
                            let uu____24967 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24967
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24972 =
                            let uu____24979 = equal t1 t2  in
                            if uu____24979
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24992 = mk_eq2 wl env orig t1 t2  in
                               match uu____24992 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24972 with
                          | (guard,wl1) ->
                              let uu____25013 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25013))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25016,FStar_Syntax_Syntax.Tm_uinst uu____25017) ->
                  let head1 =
                    let uu____25025 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25025
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25065 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25065
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25105 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25105
                    then
                      let uu____25109 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25111 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25113 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25109 uu____25111 uu____25113
                    else ());
                   (let no_free_uvars t =
                      (let uu____25127 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25127) &&
                        (let uu____25131 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25131)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25148 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25148 = FStar_Syntax_Util.Equal  in
                    let uu____25149 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25149
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25153 = equal t1 t2  in
                         (if uu____25153
                          then
                            let uu____25156 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25156
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25161 =
                            let uu____25168 = equal t1 t2  in
                            if uu____25168
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25181 = mk_eq2 wl env orig t1 t2  in
                               match uu____25181 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25161 with
                          | (guard,wl1) ->
                              let uu____25202 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25202))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25205,FStar_Syntax_Syntax.Tm_name uu____25206) ->
                  let head1 =
                    let uu____25208 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25208
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25248 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25248
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25288 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25288
                    then
                      let uu____25292 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25294 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25296 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25292 uu____25294 uu____25296
                    else ());
                   (let no_free_uvars t =
                      (let uu____25310 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25310) &&
                        (let uu____25314 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25314)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25331 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25331 = FStar_Syntax_Util.Equal  in
                    let uu____25332 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25332
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25336 = equal t1 t2  in
                         (if uu____25336
                          then
                            let uu____25339 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25339
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25344 =
                            let uu____25351 = equal t1 t2  in
                            if uu____25351
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25364 = mk_eq2 wl env orig t1 t2  in
                               match uu____25364 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25344 with
                          | (guard,wl1) ->
                              let uu____25385 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25385))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25388,FStar_Syntax_Syntax.Tm_constant uu____25389) ->
                  let head1 =
                    let uu____25391 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25391
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25431 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25431
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25471 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25471
                    then
                      let uu____25475 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25477 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25479 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25475 uu____25477 uu____25479
                    else ());
                   (let no_free_uvars t =
                      (let uu____25493 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25493) &&
                        (let uu____25497 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25497)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25514 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25514 = FStar_Syntax_Util.Equal  in
                    let uu____25515 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25515
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25519 = equal t1 t2  in
                         (if uu____25519
                          then
                            let uu____25522 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25522
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25527 =
                            let uu____25534 = equal t1 t2  in
                            if uu____25534
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25547 = mk_eq2 wl env orig t1 t2  in
                               match uu____25547 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25527 with
                          | (guard,wl1) ->
                              let uu____25568 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25568))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25571,FStar_Syntax_Syntax.Tm_fvar uu____25572) ->
                  let head1 =
                    let uu____25574 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25574
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25614 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25614
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25654 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25654
                    then
                      let uu____25658 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25660 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25662 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25658 uu____25660 uu____25662
                    else ());
                   (let no_free_uvars t =
                      (let uu____25676 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25676) &&
                        (let uu____25680 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25680)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25697 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25697 = FStar_Syntax_Util.Equal  in
                    let uu____25698 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25698
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25702 = equal t1 t2  in
                         (if uu____25702
                          then
                            let uu____25705 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25705
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25710 =
                            let uu____25717 = equal t1 t2  in
                            if uu____25717
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25730 = mk_eq2 wl env orig t1 t2  in
                               match uu____25730 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25710 with
                          | (guard,wl1) ->
                              let uu____25751 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25751))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25754,FStar_Syntax_Syntax.Tm_app uu____25755) ->
                  let head1 =
                    let uu____25773 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25773
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25813 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25813
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25853 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25853
                    then
                      let uu____25857 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25859 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25861 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25857 uu____25859 uu____25861
                    else ());
                   (let no_free_uvars t =
                      (let uu____25875 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25875) &&
                        (let uu____25879 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25879)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25896 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25896 = FStar_Syntax_Util.Equal  in
                    let uu____25897 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25897
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25901 = equal t1 t2  in
                         (if uu____25901
                          then
                            let uu____25904 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25904
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25909 =
                            let uu____25916 = equal t1 t2  in
                            if uu____25916
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25929 = mk_eq2 wl env orig t1 t2  in
                               match uu____25929 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25909 with
                          | (guard,wl1) ->
                              let uu____25950 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25950))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____25953,FStar_Syntax_Syntax.Tm_let uu____25954) ->
                  let uu____25981 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____25981
                  then
                    let uu____25984 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____25984
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____25988,uu____25989) ->
                  let uu____26003 =
                    let uu____26009 =
                      let uu____26011 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26013 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26015 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26017 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26011 uu____26013 uu____26015 uu____26017
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26009)
                     in
                  FStar_Errors.raise_error uu____26003
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26021,FStar_Syntax_Syntax.Tm_let uu____26022) ->
                  let uu____26036 =
                    let uu____26042 =
                      let uu____26044 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26046 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26048 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26050 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26044 uu____26046 uu____26048 uu____26050
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26042)
                     in
                  FStar_Errors.raise_error uu____26036
                    t1.FStar_Syntax_Syntax.pos
              | uu____26054 -> giveup env "head tag mismatch" orig))))

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
          (let uu____26118 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26118
           then
             let uu____26123 =
               let uu____26125 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26125  in
             let uu____26126 =
               let uu____26128 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26128  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26123 uu____26126
           else ());
          (let uu____26132 =
             let uu____26134 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26134  in
           if uu____26132
           then
             let uu____26137 =
               let uu____26139 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____26141 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____26139 uu____26141
                in
             giveup env uu____26137 orig
           else
             (let uu____26146 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____26146 with
              | (ret_sub_prob,wl1) ->
                  let uu____26154 =
                    FStar_List.fold_right2
                      (fun uu____26191  ->
                         fun uu____26192  ->
                           fun uu____26193  ->
                             match (uu____26191, uu____26192, uu____26193)
                             with
                             | ((a1,uu____26237),(a2,uu____26239),(arg_sub_probs,wl2))
                                 ->
                                 let uu____26272 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____26272 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____26154 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____26302 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____26302  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____26310 = attempt sub_probs wl3  in
                       solve env uu____26310)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____26333 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____26336)::[] -> wp1
              | uu____26361 ->
                  let uu____26372 =
                    let uu____26374 =
                      let uu____26376 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____26376  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____26374
                     in
                  failwith uu____26372
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____26383 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____26383]
              | x -> x  in
            let uu____26385 =
              let uu____26396 =
                let uu____26405 =
                  let uu____26406 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____26406 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____26405  in
              [uu____26396]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____26385;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____26424 = lift_c1 ()  in solve_eq uu____26424 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___354_26433  ->
                       match uu___354_26433 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____26438 -> false))
                in
             let uu____26440 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____26470)::uu____26471,(wp2,uu____26473)::uu____26474)
                   -> (wp1, wp2)
               | uu____26547 ->
                   let uu____26572 =
                     let uu____26578 =
                       let uu____26580 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____26582 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____26580 uu____26582
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____26578)
                      in
                   FStar_Errors.raise_error uu____26572
                     env.FStar_TypeChecker_Env.range
                in
             match uu____26440 with
             | (wpc1,wpc2) ->
                 let uu____26592 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____26592
                 then
                   let uu____26597 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____26597 wl
                 else
                   (let uu____26601 =
                      let uu____26608 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____26608  in
                    match uu____26601 with
                    | (c2_decl,qualifiers) ->
                        let uu____26629 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____26629
                        then
                          let c1_repr =
                            let uu____26636 =
                              let uu____26637 =
                                let uu____26638 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____26638  in
                              let uu____26639 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26637 uu____26639
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26636
                             in
                          let c2_repr =
                            let uu____26641 =
                              let uu____26642 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____26643 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____26642 uu____26643
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____26641
                             in
                          let uu____26644 =
                            let uu____26649 =
                              let uu____26651 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____26653 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____26651 uu____26653
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____26649
                             in
                          (match uu____26644 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____26659 = attempt [prob] wl2  in
                               solve env uu____26659)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____26674 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26674
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____26683 =
                                     let uu____26690 =
                                       let uu____26691 =
                                         let uu____26708 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____26711 =
                                           let uu____26722 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____26731 =
                                             let uu____26742 =
                                               let uu____26751 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____26751
                                                in
                                             [uu____26742]  in
                                           uu____26722 :: uu____26731  in
                                         (uu____26708, uu____26711)  in
                                       FStar_Syntax_Syntax.Tm_app uu____26691
                                        in
                                     FStar_Syntax_Syntax.mk uu____26690  in
                                   uu____26683 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____26803 =
                                    let uu____26810 =
                                      let uu____26811 =
                                        let uu____26828 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____26831 =
                                          let uu____26842 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____26851 =
                                            let uu____26862 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____26871 =
                                              let uu____26882 =
                                                let uu____26891 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____26891
                                                 in
                                              [uu____26882]  in
                                            uu____26862 :: uu____26871  in
                                          uu____26842 :: uu____26851  in
                                        (uu____26828, uu____26831)  in
                                      FStar_Syntax_Syntax.Tm_app uu____26811
                                       in
                                    FStar_Syntax_Syntax.mk uu____26810  in
                                  uu____26803 FStar_Pervasives_Native.None r)
                              in
                           (let uu____26948 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____26948
                            then
                              let uu____26953 =
                                let uu____26955 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____26955
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____26953
                            else ());
                           (let uu____26959 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____26959 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____26968 =
                                    let uu____26971 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_12  ->
                                         FStar_Pervasives_Native.Some _0_12)
                                      uu____26971
                                     in
                                  solve_prob orig uu____26968 [] wl1  in
                                let uu____26974 = attempt [base_prob] wl2  in
                                solve env uu____26974))))
           in
        let uu____26975 = FStar_Util.physical_equality c1 c2  in
        if uu____26975
        then
          let uu____26978 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____26978
        else
          ((let uu____26982 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____26982
            then
              let uu____26987 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____26989 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____26987
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____26989
            else ());
           (let uu____26994 =
              let uu____27003 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____27006 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____27003, uu____27006)  in
            match uu____26994 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27024),FStar_Syntax_Syntax.Total
                    (t2,uu____27026)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____27043 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27043 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27045,FStar_Syntax_Syntax.Total uu____27046) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27065),FStar_Syntax_Syntax.Total
                    (t2,uu____27067)) ->
                     let uu____27084 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27084 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____27087),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27089)) ->
                     let uu____27106 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27106 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____27109),FStar_Syntax_Syntax.GTotal
                    (t2,uu____27111)) ->
                     let uu____27128 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____27128 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____27130,FStar_Syntax_Syntax.Comp uu____27131) ->
                     let uu____27140 =
                       let uu___411_27143 = problem  in
                       let uu____27146 =
                         let uu____27147 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27147
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___411_27143.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27146;
                         FStar_TypeChecker_Common.relation =
                           (uu___411_27143.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___411_27143.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___411_27143.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___411_27143.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___411_27143.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___411_27143.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___411_27143.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___411_27143.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27140 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____27148,FStar_Syntax_Syntax.Comp uu____27149) ->
                     let uu____27158 =
                       let uu___411_27161 = problem  in
                       let uu____27164 =
                         let uu____27165 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27165
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___411_27161.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27164;
                         FStar_TypeChecker_Common.relation =
                           (uu___411_27161.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___411_27161.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___411_27161.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___411_27161.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___411_27161.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___411_27161.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___411_27161.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___411_27161.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27158 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27166,FStar_Syntax_Syntax.GTotal uu____27167) ->
                     let uu____27176 =
                       let uu___412_27179 = problem  in
                       let uu____27182 =
                         let uu____27183 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27183
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___412_27179.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___412_27179.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___412_27179.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27182;
                         FStar_TypeChecker_Common.element =
                           (uu___412_27179.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___412_27179.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___412_27179.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___412_27179.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___412_27179.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___412_27179.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27176 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27184,FStar_Syntax_Syntax.Total uu____27185) ->
                     let uu____27194 =
                       let uu___412_27197 = problem  in
                       let uu____27200 =
                         let uu____27201 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27201
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___412_27197.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___412_27197.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___412_27197.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27200;
                         FStar_TypeChecker_Common.element =
                           (uu___412_27197.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___412_27197.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___412_27197.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___412_27197.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___412_27197.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___412_27197.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____27194 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____27202,FStar_Syntax_Syntax.Comp uu____27203) ->
                     let uu____27204 =
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
                     if uu____27204
                     then
                       let uu____27207 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____27207 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27214 =
                            let uu____27219 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____27219
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27228 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____27229 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____27228, uu____27229))
                             in
                          match uu____27214 with
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
                           (let uu____27237 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____27237
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____27245 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____27245 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____27248 =
                                  let uu____27250 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____27252 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____27250 uu____27252
                                   in
                                giveup env uu____27248 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____27263 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____27263 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____27313 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____27313 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____27338 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27369  ->
                match uu____27369 with
                | (u1,u2) ->
                    let uu____27377 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____27379 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____27377 uu____27379))
         in
      FStar_All.pipe_right uu____27338 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____27416,[])) when
          let uu____27443 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____27443 -> "{}"
      | uu____27446 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27473 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____27473
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____27485 =
              FStar_List.map
                (fun uu____27498  ->
                   match uu____27498 with
                   | (uu____27505,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____27485 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____27516 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____27516 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_TypeChecker_Common.prob,worklist)
                  FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____27573 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____27573
                  then
                    let uu____27581 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____27583 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27581
                      (rel_to_string rel) uu____27583
                  else "TOP"  in
                let uu____27589 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____27589 with
                | (p,wl1) ->
                    (def_check_prob (Prims.strcat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv,worklist)
              FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____27649 =
                let uu____27652 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_13  -> FStar_Pervasives_Native.Some _0_13)
                  uu____27652
                 in
              FStar_Syntax_Syntax.new_bv uu____27649 t1  in
            let uu____27655 =
              let uu____27660 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27660
               in
            match uu____27655 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
           FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____27738 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____27738
              then
                let uu____27745 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____27745
              else ());
             (let result = err (d, s)  in
              FStar_Syntax_Unionfind.rollback tx; result))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____27772 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____27772
            then
              let uu____27777 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27777
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____27784 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____27784
             then
               let uu____27789 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27789
             else ());
            (let f2 =
               let uu____27795 =
                 let uu____27796 = FStar_Syntax_Util.unmeta f1  in
                 uu____27796.FStar_Syntax_Syntax.n  in
               match uu____27795 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27800 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___413_27801 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___413_27801.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___413_27801.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___413_27801.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicit
                                           Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____27856 =
              let uu____27857 =
                let uu____27858 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_14  -> FStar_TypeChecker_Common.NonTrivial _0_14)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____27858;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____27857  in
            FStar_All.pipe_left
              (fun _0_15  -> FStar_Pervasives_Native.Some _0_15) uu____27856
  
let with_guard_no_simp :
  'Auu____27874 .
    'Auu____27874 ->
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
            let uu____27897 =
              let uu____27898 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____27898;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____27897
  
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
          (let uu____27931 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____27931
           then
             let uu____27936 = FStar_Syntax_Print.term_to_string t1  in
             let uu____27938 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____27936
               uu____27938
           else ());
          (let uu____27943 =
             let uu____27948 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____27948
              in
           match uu____27943 with
           | (prob,wl) ->
               let g =
                 let uu____27956 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____27966  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____27956  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____28002 = try_teq true env t1 t2  in
        match uu____28002 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____28007 = FStar_TypeChecker_Env.get_range env  in
              let uu____28008 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____28007 uu____28008);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28016 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____28016
              then
                let uu____28021 = FStar_Syntax_Print.term_to_string t1  in
                let uu____28023 = FStar_Syntax_Print.term_to_string t2  in
                let uu____28025 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28021
                  uu____28023 uu____28025
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
          let uu____28051 = FStar_TypeChecker_Env.get_range env  in
          let uu____28052 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____28051 uu____28052
  
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
        (let uu____28081 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28081
         then
           let uu____28086 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____28088 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28086 uu____28088
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28099 =
           let uu____28106 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28106 "sub_comp"
            in
         match uu____28099 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____28119 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____28130  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____28119)))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____28177  ->
        match uu____28177 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28220 =
                 let uu____28226 =
                   let uu____28228 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____28230 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28228 uu____28230
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28226)  in
               let uu____28234 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____28220 uu____28234)
               in
            let equiv1 v1 v' =
              let uu____28247 =
                let uu____28252 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____28253 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____28252, uu____28253)  in
              match uu____28247 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28273 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____28304 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____28304 with
                      | FStar_Syntax_Syntax.U_unif uu____28311 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28340  ->
                                    match uu____28340 with
                                    | (u,v') ->
                                        let uu____28349 = equiv1 v1 v'  in
                                        if uu____28349
                                        then
                                          let uu____28354 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____28354 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____28375 -> []))
               in
            let uu____28380 =
              let wl =
                let uu___414_28384 = empty_worklist env  in
                {
                  attempting = (uu___414_28384.attempting);
                  wl_deferred = (uu___414_28384.wl_deferred);
                  ctr = (uu___414_28384.ctr);
                  defer_ok = false;
                  smt_ok = (uu___414_28384.smt_ok);
                  umax_heuristic_ok = (uu___414_28384.umax_heuristic_ok);
                  tcenv = (uu___414_28384.tcenv);
                  wl_implicits = (uu___414_28384.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28403  ->
                      match uu____28403 with
                      | (lb,v1) ->
                          let uu____28410 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____28410 with
                           | USolved wl1 -> ()
                           | uu____28413 -> fail1 lb v1)))
               in
            let rec check_ineq uu____28424 =
              match uu____28424 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____28436) -> true
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
                      uu____28460,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____28462,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____28473) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____28481,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____28490 -> false)
               in
            let uu____28496 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28513  ->
                      match uu____28513 with
                      | (u,v1) ->
                          let uu____28521 = check_ineq (u, v1)  in
                          if uu____28521
                          then true
                          else
                            ((let uu____28529 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____28529
                              then
                                let uu____28534 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____28536 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____28534
                                  uu____28536
                              else ());
                             false)))
               in
            if uu____28496
            then ()
            else
              ((let uu____28546 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____28546
                then
                  ((let uu____28552 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28552);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28564 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28564))
                else ());
               (let uu____28577 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28577))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> unit)
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
        let fail1 uu____28651 =
          match uu____28651 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___415_28677 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___415_28677.attempting);
            wl_deferred = (uu___415_28677.wl_deferred);
            ctr = (uu___415_28677.ctr);
            defer_ok;
            smt_ok = (uu___415_28677.smt_ok);
            umax_heuristic_ok = (uu___415_28677.umax_heuristic_ok);
            tcenv = (uu___415_28677.tcenv);
            wl_implicits = (uu___415_28677.wl_implicits)
          }  in
        (let uu____28680 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____28680
         then
           let uu____28685 = FStar_Util.string_of_bool defer_ok  in
           let uu____28687 = wl_to_string wl  in
           let uu____28689 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____28685 uu____28687 uu____28689
         else ());
        (let g1 =
           let uu____28695 = solve_and_commit env wl fail1  in
           match uu____28695 with
           | FStar_Pervasives_Native.Some
               (uu____28702::uu____28703,uu____28704) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___416_28733 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___416_28733.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___416_28733.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____28734 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___417_28743 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___417_28743.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___417_28743.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___417_28743.FStar_TypeChecker_Env.implicits)
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
    let uu____28797 = FStar_ST.op_Bang last_proof_ns  in
    match uu____28797 with
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
            let uu___418_28922 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___418_28922.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___418_28922.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___418_28922.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____28923 =
            let uu____28925 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____28925  in
          if uu____28923
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____28937 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____28938 =
                       let uu____28940 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____28940
                        in
                     FStar_Errors.diag uu____28937 uu____28938)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____28948 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____28949 =
                        let uu____28951 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____28951
                         in
                      FStar_Errors.diag uu____28948 uu____28949)
                   else ();
                   (let uu____28957 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____28957
                      "discharge_guard'" env vc1);
                   (let uu____28959 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____28959 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____28968 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____28969 =
                                let uu____28971 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____28971
                                 in
                              FStar_Errors.diag uu____28968 uu____28969)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____28981 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____28982 =
                                let uu____28984 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____28984
                                 in
                              FStar_Errors.diag uu____28981 uu____28982)
                           else ();
                           (let vcs =
                              let uu____28998 = FStar_Options.use_tactics ()
                                 in
                              if uu____28998
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____29020  ->
                                     (let uu____29022 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____29022);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____29066  ->
                                              match uu____29066 with
                                              | (env1,goal,opts) ->
                                                  let uu____29082 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____29082, opts)))))
                              else
                                (let uu____29085 =
                                   let uu____29092 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____29092)  in
                                 [uu____29085])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____29125  ->
                                    match uu____29125 with
                                    | (env1,goal,opts) ->
                                        let uu____29135 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____29135 with
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
                                                (let uu____29147 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29148 =
                                                   let uu____29150 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____29152 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____29150 uu____29152
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29147 uu____29148)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____29159 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____29160 =
                                                   let uu____29162 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____29162
                                                    in
                                                 FStar_Errors.diag
                                                   uu____29159 uu____29160)
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
      let uu____29180 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____29180 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____29189 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29189
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____29203 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____29203 with
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
        let uu____29233 = try_teq false env t1 t2  in
        match uu____29233 with
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
          let unresolved ctx_u =
            let uu____29277 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____29277 with
            | FStar_Pervasives_Native.Some uu____29281 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____29305 = acc  in
            match uu____29305 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____29324 = hd1  in
                     (match uu____29324 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____29329;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____29342 = unresolved ctx_u  in
                             if uu____29342
                             then
                               match hd1.FStar_TypeChecker_Env.imp_meta with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env1,tau) ->
                                   ((let uu____29357 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____29357
                                     then
                                       let uu____29361 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____29361
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____29370 = teq_nosmt env1 t tm
                                          in
                                       match uu____29370 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let hd2 =
                                       let uu___419_29380 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___419_29380.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           (uu___419_29380.FStar_TypeChecker_Env.imp_uvar);
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___419_29380.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___419_29380.FStar_TypeChecker_Env.imp_range);
                                         FStar_TypeChecker_Env.imp_meta =
                                           FStar_Pervasives_Native.None
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
                                    let uu___420_29395 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___420_29395.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___420_29395.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___420_29395.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___420_29395.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___420_29395.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___420_29395.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___420_29395.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___420_29395.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___420_29395.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___420_29395.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___420_29395.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___420_29395.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___420_29395.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___420_29395.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___420_29395.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___420_29395.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___420_29395.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___420_29395.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___420_29395.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___420_29395.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___420_29395.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___420_29395.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___420_29395.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___420_29395.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___420_29395.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___420_29395.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___420_29395.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___420_29395.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___420_29395.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___420_29395.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___420_29395.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___420_29395.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___420_29395.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___420_29395.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___420_29395.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___420_29395.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___420_29395.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___420_29395.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___420_29395.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___420_29395.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___420_29395.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___420_29395.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___421_29399 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___421_29399.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___421_29399.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___421_29399.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___421_29399.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___421_29399.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___421_29399.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___421_29399.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___421_29399.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___421_29399.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___421_29399.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___421_29399.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___421_29399.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___421_29399.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___421_29399.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___421_29399.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___421_29399.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___421_29399.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___421_29399.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___421_29399.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___421_29399.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___421_29399.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___421_29399.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___421_29399.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___421_29399.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___421_29399.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___421_29399.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___421_29399.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___421_29399.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___421_29399.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___421_29399.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___421_29399.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___421_29399.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___421_29399.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___421_29399.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___421_29399.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___421_29399.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___421_29399.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___421_29399.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___421_29399.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___421_29399.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___421_29399.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___421_29399.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____29404 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____29404
                                   then
                                     let uu____29409 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____29411 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____29413 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____29415 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____29409 uu____29411 uu____29413
                                       reason uu____29415
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___423_29422  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____29429 =
                                             let uu____29439 =
                                               let uu____29447 =
                                                 let uu____29449 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____29451 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____29453 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____29449 uu____29451
                                                   uu____29453
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____29447, r)
                                                in
                                             [uu____29439]  in
                                           FStar_Errors.add_errors
                                             uu____29429);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___424_29473 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___424_29473.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___424_29473.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___424_29473.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____29477 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____29488  ->
                                               let uu____29489 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____29491 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____29493 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____29489 uu____29491
                                                 reason uu____29493)) env2 g2
                                         true
                                        in
                                     match uu____29477 with
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
          let uu___425_29501 = g  in
          let uu____29502 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___425_29501.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___425_29501.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___425_29501.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____29502
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
        let uu____29545 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____29545 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____29546 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____29546
      | imp::uu____29548 ->
          let uu____29551 =
            let uu____29557 =
              let uu____29559 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____29561 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____29559 uu____29561 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29557)
             in
          FStar_Errors.raise_error uu____29551
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29583 = teq_nosmt env t1 t2  in
        match uu____29583 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___426_29602 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___426_29602.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___426_29602.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___426_29602.FStar_TypeChecker_Env.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____29638 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29638
         then
           let uu____29643 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____29645 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29643
             uu____29645
         else ());
        (let uu____29650 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____29650 with
         | (prob,x,wl) ->
             let g =
               let uu____29669 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29680  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____29669  in
             ((let uu____29701 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____29701
               then
                 let uu____29706 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____29708 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____29710 =
                   let uu____29712 = FStar_Util.must g  in
                   guard_to_string env uu____29712  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29706 uu____29708 uu____29710
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
        let uu____29749 = check_subtyping env t1 t2  in
        match uu____29749 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29768 =
              let uu____29769 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____29769 g  in
            FStar_Pervasives_Native.Some uu____29768
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29788 = check_subtyping env t1 t2  in
        match uu____29788 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____29807 =
              let uu____29808 =
                let uu____29809 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____29809]  in
              FStar_TypeChecker_Env.close_guard env uu____29808 g  in
            FStar_Pervasives_Native.Some uu____29807
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____29847 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29847
         then
           let uu____29852 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____29854 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29852
             uu____29854
         else ());
        (let uu____29859 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____29859 with
         | (prob,x,wl) ->
             let g =
               let uu____29874 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____29885  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____29874  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____29909 =
                      let uu____29910 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____29910]  in
                    FStar_TypeChecker_Env.close_guard env uu____29909 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29951 = subtype_nosmt env t1 t2  in
        match uu____29951 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  