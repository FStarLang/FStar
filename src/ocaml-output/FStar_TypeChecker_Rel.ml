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
    match projectee with | TERM _0 -> true | uu____34 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____64 -> false
  
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
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Env.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__smt_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
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
                  let uu____351 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____351;
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
                     FStar_TypeChecker_Env.imp_range = r
                   }  in
                 (ctx_uvar, t,
                   (let uu___335_382 = wl  in
                    {
                      attempting = (uu___335_382.attempting);
                      wl_deferred = (uu___335_382.wl_deferred);
                      ctr = (uu___335_382.ctr);
                      defer_ok = (uu___335_382.defer_ok);
                      smt_ok = (uu___335_382.smt_ok);
                      tcenv = (uu___335_382.tcenv);
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
            let uu___336_414 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___336_414.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___336_414.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___336_414.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___336_414.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___336_414.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___336_414.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___336_414.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___336_414.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___336_414.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___336_414.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___336_414.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___336_414.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___336_414.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___336_414.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___336_414.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___336_414.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___336_414.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___336_414.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___336_414.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___336_414.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___336_414.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___336_414.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___336_414.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___336_414.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___336_414.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___336_414.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___336_414.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___336_414.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___336_414.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___336_414.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___336_414.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___336_414.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___336_414.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___336_414.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___336_414.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___336_414.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___336_414.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___336_414.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___336_414.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___336_414.FStar_TypeChecker_Env.dep_graph)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____416 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____416 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____451 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____481 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____506 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____512 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____518 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___302_533  ->
    match uu___302_533 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____539 = FStar_Syntax_Util.head_and_args t  in
    match uu____539 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____594 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____595 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____607 =
                     let uu____608 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____608  in
                   FStar_Util.format1 "@<%s>" uu____607
                in
             let uu____611 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____594 uu____595 uu____611
         | uu____612 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___303_622  ->
      match uu___303_622 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____626 =
            let uu____629 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____630 =
              let uu____633 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____634 =
                let uu____637 =
                  let uu____640 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____640]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____637
                 in
              uu____633 :: uu____634  in
            uu____629 :: uu____630  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____626
      | FStar_TypeChecker_Common.CProb p ->
          let uu____644 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____645 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____646 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____644 uu____645
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____646
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___304_656  ->
      match uu___304_656 with
      | UNIV (u,t) ->
          let x =
            let uu____660 = FStar_Options.hide_uvar_nums ()  in
            if uu____660
            then "?"
            else
              (let uu____662 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____662 FStar_Util.string_of_int)
             in
          let uu____663 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____663
      | TERM (u,t) ->
          let x =
            let uu____667 = FStar_Options.hide_uvar_nums ()  in
            if uu____667
            then "?"
            else
              (let uu____669 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____669 FStar_Util.string_of_int)
             in
          let uu____670 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____670
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____685 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____685 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____699 =
      let uu____702 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____702
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____699 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____715 .
    (FStar_Syntax_Syntax.term,'Auu____715) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____733 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____751  ->
              match uu____751 with
              | (x,uu____757) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____733 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = true;
      smt_ok = true;
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
        (let uu____787 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____787
         then
           let uu____788 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____788
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___305_794  ->
    match uu___305_794 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____799 .
    'Auu____799 FStar_TypeChecker_Common.problem ->
      'Auu____799 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___337_811 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___337_811.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___337_811.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___337_811.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___337_811.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___337_811.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___337_811.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___337_811.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____818 .
    'Auu____818 FStar_TypeChecker_Common.problem ->
      'Auu____818 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___306_835  ->
    match uu___306_835 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___307_850  ->
    match uu___307_850 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___338_856 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___338_856.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___338_856.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___338_856.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___338_856.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___338_856.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___338_856.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___338_856.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___338_856.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___338_856.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___339_864 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___339_864.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___339_864.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___339_864.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___339_864.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___339_864.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___339_864.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___339_864.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___339_864.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___339_864.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___308_876  ->
      match uu___308_876 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___309_881  ->
    match uu___309_881 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___310_892  ->
    match uu___310_892 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___311_905  ->
    match uu___311_905 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___312_918  ->
    match uu___312_918 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___313_931  ->
    match uu___313_931 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___314_944  ->
    match uu___314_944 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___315_955  ->
    match uu___315_955 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____970 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____970) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____998 =
          let uu____999 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____999  in
        if uu____998
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1033)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1073 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1091 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1091]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1073
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1111 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1129 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1129]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1111
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1162 =
          let uu____1163 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1163  in
        if uu____1162
        then ()
        else
          (let uu____1165 =
             let uu____1168 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1168
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1165 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1206 =
          let uu____1207 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1207  in
        if uu____1206
        then ()
        else
          (let uu____1209 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1209)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1224 =
        let uu____1225 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1225  in
      if uu____1224
      then ()
      else
        (let msgf m =
           let uu____1233 =
             let uu____1234 =
               let uu____1235 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1235 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1234  in
           Prims.strcat msg uu____1233  in
         (let uu____1237 = msgf "scope"  in
          let uu____1238 = p_scope prob  in
          def_scope_wf uu____1237 (p_loc prob) uu____1238);
         (let uu____1246 = msgf "guard"  in
          def_check_scoped uu____1246 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1251 = msgf "lhs"  in
                def_check_scoped uu____1251 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1252 = msgf "rhs"  in
                def_check_scoped uu____1252 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1257 = msgf "lhs"  in
                def_check_scoped_comp uu____1257 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1258 = msgf "rhs"  in
                def_check_scoped_comp uu____1258 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___340_1274 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___340_1274.wl_deferred);
          ctr = (uu___340_1274.ctr);
          defer_ok = (uu___340_1274.defer_ok);
          smt_ok;
          tcenv = (uu___340_1274.tcenv);
          wl_implicits = (uu___340_1274.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1281 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1281,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___341_1304 = empty_worklist env  in
      let uu____1305 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1305;
        wl_deferred = (uu___341_1304.wl_deferred);
        ctr = (uu___341_1304.ctr);
        defer_ok = (uu___341_1304.defer_ok);
        smt_ok = (uu___341_1304.smt_ok);
        tcenv = (uu___341_1304.tcenv);
        wl_implicits = (uu___341_1304.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___342_1325 = wl  in
        {
          attempting = (uu___342_1325.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___342_1325.ctr);
          defer_ok = (uu___342_1325.defer_ok);
          smt_ok = (uu___342_1325.smt_ok);
          tcenv = (uu___342_1325.tcenv);
          wl_implicits = (uu___342_1325.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___343_1347 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___343_1347.wl_deferred);
         ctr = (uu___343_1347.ctr);
         defer_ok = (uu___343_1347.defer_ok);
         smt_ok = (uu___343_1347.smt_ok);
         tcenv = (uu___343_1347.tcenv);
         wl_implicits = (uu___343_1347.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1358 .
    worklist ->
      'Auu____1358 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1387 = FStar_Syntax_Util.type_u ()  in
          match uu____1387 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1399 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1399 with
               | (uu____1410,tt,wl1) ->
                   let uu____1413 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1413, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___316_1418  ->
    match uu___316_1418 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1434 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1434 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1444  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1542 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1542 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1542 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1542 FStar_TypeChecker_Common.problem,worklist)
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
                        let uu____1619 =
                          let uu____1626 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1626]  in
                        FStar_List.append scope uu____1619
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____1657 =
                      let uu____1660 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____1660  in
                    FStar_List.append uu____1657
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____1673 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1673 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____1692 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____1692;
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
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
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
                  (let uu____1756 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1756 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
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
                  (let uu____1835 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1835 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____1871 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1871 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1871 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____1871 FStar_TypeChecker_Common.problem,worklist)
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
                          let uu____1935 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1935]  in
                        let uu____1948 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____1948
                     in
                  let uu____1951 =
                    let uu____1958 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___344_1966 = wl  in
                       {
                         attempting = (uu___344_1966.attempting);
                         wl_deferred = (uu___344_1966.wl_deferred);
                         ctr = (uu___344_1966.ctr);
                         defer_ok = (uu___344_1966.defer_ok);
                         smt_ok = (uu___344_1966.smt_ok);
                         tcenv = env;
                         wl_implicits = (uu___344_1966.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____1958
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1951 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____1978 =
                              let uu____1983 =
                                let uu____1984 =
                                  let uu____1991 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____1991
                                   in
                                [uu____1984]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____1983  in
                            uu____1978 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2015 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2015;
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
                let uu____2057 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2057;
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
  'Auu____2069 .
    worklist ->
      'Auu____2069 FStar_TypeChecker_Common.problem ->
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
              let uu____2102 =
                let uu____2105 =
                  let uu____2106 =
                    let uu____2113 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2113)  in
                  FStar_Syntax_Syntax.NT uu____2106  in
                [uu____2105]  in
              FStar_Syntax_Subst.subst uu____2102 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2133 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2133
        then
          let uu____2134 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2135 = prob_to_string env d  in
          let uu____2136 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2134 uu____2135 uu____2136 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2142 -> failwith "impossible"  in
           let uu____2143 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2155 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2156 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2155, uu____2156)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2160 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2161 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2160, uu____2161)
              in
           match uu____2143 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___317_2179  ->
            match uu___317_2179 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2191 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2195 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2195 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___318_2220  ->
           match uu___318_2220 with
           | UNIV uu____2223 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2230 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2230
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
        (fun uu___319_2254  ->
           match uu___319_2254 with
           | UNIV (u',t) ->
               let uu____2259 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2259
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2263 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2274 =
        let uu____2275 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2275
         in
      FStar_Syntax_Subst.compress uu____2274
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2286 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2286
  
let norm_arg :
  'Auu____2293 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2293) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2293)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2316 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2316, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____2357  ->
              match uu____2357 with
              | (x,imp) ->
                  let uu____2368 =
                    let uu___345_2369 = x  in
                    let uu____2370 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___345_2369.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___345_2369.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2370
                    }  in
                  (uu____2368, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2391 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2391
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2395 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2395
        | uu____2398 -> u2  in
      let uu____2399 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2399
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                FStar_Syntax_Syntax.term'
                                                                  FStar_Syntax_Syntax.syntax)
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
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF]
             in
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
                (let uu____2521 = norm_refinement env t12  in
                 match uu____2521 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2538;
                     FStar_Syntax_Syntax.vars = uu____2539;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2565 =
                       let uu____2566 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2567 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2566 uu____2567
                        in
                     failwith uu____2565)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2583 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2583
          | FStar_Syntax_Syntax.Tm_uinst uu____2584 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2623 =
                   let uu____2624 = FStar_Syntax_Subst.compress t1'  in
                   uu____2624.FStar_Syntax_Syntax.n  in
                 match uu____2623 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2641 -> aux true t1'
                 | uu____2648 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2665 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2698 =
                   let uu____2699 = FStar_Syntax_Subst.compress t1'  in
                   uu____2699.FStar_Syntax_Syntax.n  in
                 match uu____2698 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2716 -> aux true t1'
                 | uu____2723 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2740 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2787 =
                   let uu____2788 = FStar_Syntax_Subst.compress t1'  in
                   uu____2788.FStar_Syntax_Syntax.n  in
                 match uu____2787 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2805 -> aux true t1'
                 | uu____2812 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2829 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2846 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2863 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2880 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2897 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2926 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____2959 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2982 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3011 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3040 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3079 ->
              let uu____3086 =
                let uu____3087 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3088 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3087 uu____3088
                 in
              failwith uu____3086
          | FStar_Syntax_Syntax.Tm_ascribed uu____3103 ->
              let uu____3130 =
                let uu____3131 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3132 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3131 uu____3132
                 in
              failwith uu____3130
          | FStar_Syntax_Syntax.Tm_delayed uu____3147 ->
              let uu____3170 =
                let uu____3171 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3172 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3171 uu____3172
                 in
              failwith uu____3170
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3187 =
                let uu____3188 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3189 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3188 uu____3189
                 in
              failwith uu____3187
           in
        let uu____3204 = whnf env t1  in aux false uu____3204
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Normalize.steps ->
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
      let uu____3260 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3260 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3300 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3300, FStar_Syntax_Util.t_true)
  
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
        let uu____3324 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3324 with
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
  fun uu____3403  ->
    match uu____3403 with
    | (t_base,refopt) ->
        let uu____3434 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3434 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3472 =
      let uu____3475 =
        let uu____3478 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3501  ->
                  match uu____3501 with | (uu____3508,uu____3509,x) -> x))
           in
        FStar_List.append wl.attempting uu____3478  in
      FStar_List.map (wl_prob_to_string wl) uu____3475  in
    FStar_All.pipe_right uu____3472 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____3523 .
    ('Auu____3523,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3534  ->
    match uu____3534 with
    | (uu____3541,c,args) ->
        let uu____3544 = print_ctx_uvar c  in
        let uu____3545 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3544 uu____3545
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3551 = FStar_Syntax_Util.head_and_args t  in
    match uu____3551 with
    | (head1,_args) ->
        let uu____3588 =
          let uu____3589 = FStar_Syntax_Subst.compress head1  in
          uu____3589.FStar_Syntax_Syntax.n  in
        (match uu____3588 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3592 -> true
         | uu____3605 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3611 = FStar_Syntax_Util.head_and_args t  in
    match uu____3611 with
    | (head1,_args) ->
        let uu____3648 =
          let uu____3649 = FStar_Syntax_Subst.compress head1  in
          uu____3649.FStar_Syntax_Syntax.n  in
        (match uu____3648 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____3653) -> u
         | uu____3670 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____3693 = FStar_Syntax_Util.head_and_args t  in
      match uu____3693 with
      | (head1,args) ->
          let uu____3734 =
            let uu____3735 = FStar_Syntax_Subst.compress head1  in
            uu____3735.FStar_Syntax_Syntax.n  in
          (match uu____3734 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____3743)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____3776 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___320_3801  ->
                         match uu___320_3801 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____3805 =
                               let uu____3806 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____3806.FStar_Syntax_Syntax.n  in
                             (match uu____3805 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____3810 -> false)
                         | uu____3811 -> true))
                  in
               (match uu____3776 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____3833 =
                        FStar_List.collect
                          (fun uu___321_3843  ->
                             match uu___321_3843 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____3847 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____3847]
                             | uu____3848 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____3833 FStar_List.rev  in
                    let uu____3865 =
                      let uu____3872 =
                        let uu____3879 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___322_3897  ->
                                  match uu___322_3897 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____3901 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____3901]
                                  | uu____3902 -> []))
                           in
                        FStar_All.pipe_right uu____3879 FStar_List.rev  in
                      let uu____3919 =
                        let uu____3922 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____3922  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____3872 uu____3919
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____3865 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____3951  ->
                                match uu____3951 with
                                | (x,i) ->
                                    let uu____3962 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____3962, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____3985  ->
                                match uu____3985 with
                                | (a,i) ->
                                    let uu____3996 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____3996, i)) args_sol
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
           | uu____4012 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4032 =
          let uu____4053 =
            let uu____4054 = FStar_Syntax_Subst.compress k  in
            uu____4054.FStar_Syntax_Syntax.n  in
          match uu____4053 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4123 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4123)
              else
                (let uu____4153 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4153 with
                 | (ys',t1,uu____4184) ->
                     let uu____4189 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4189))
          | uu____4222 ->
              let uu____4223 =
                let uu____4228 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4228)  in
              ((ys, t), uu____4223)
           in
        match uu____4032 with
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
                 let uu____4305 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4305 c  in
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
               (let uu____4379 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4379
                then
                  let uu____4380 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4381 = print_ctx_uvar uv  in
                  let uu____4382 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4380 uu____4381 uu____4382
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4388 =
                   let uu____4389 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4389  in
                 let uu____4390 =
                   let uu____4393 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4393
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____4388 uu____4390 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____4418 =
               let uu____4419 =
                 let uu____4420 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____4421 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____4420 uu____4421
                  in
               failwith uu____4419  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____4471  ->
                       match uu____4471 with
                       | (a,i) ->
                           let uu____4484 =
                             let uu____4485 = FStar_Syntax_Subst.compress a
                                in
                             uu____4485.FStar_Syntax_Syntax.n  in
                           (match uu____4484 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____4503 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____4511 =
                 let uu____4512 = is_flex g  in Prims.op_Negation uu____4512
                  in
               if uu____4511
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____4516 = destruct_flex_t g wl  in
                  match uu____4516 with
                  | ((uu____4521,uv1,args),wl1) ->
                      ((let uu____4526 = args_as_binders args  in
                        assign_solution uu____4526 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___346_4528 = wl1  in
              {
                attempting = (uu___346_4528.attempting);
                wl_deferred = (uu___346_4528.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___346_4528.defer_ok);
                smt_ok = (uu___346_4528.smt_ok);
                tcenv = (uu___346_4528.tcenv);
                wl_implicits = (uu___346_4528.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4549 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4549
         then
           let uu____4550 = FStar_Util.string_of_int pid  in
           let uu____4551 =
             let uu____4552 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4552 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4550 uu____4551
         else ());
        commit sol;
        (let uu___347_4559 = wl  in
         {
           attempting = (uu___347_4559.attempting);
           wl_deferred = (uu___347_4559.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___347_4559.defer_ok);
           smt_ok = (uu___347_4559.smt_ok);
           tcenv = (uu___347_4559.tcenv);
           wl_implicits = (uu___347_4559.wl_implicits)
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
             | (uu____4621,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4649 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4649
              in
           (let uu____4655 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4655
            then
              let uu____4656 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4657 =
                let uu____4658 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4658 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4656 uu____4657
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
        let uu____4683 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4683 FStar_Util.set_elements  in
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
      let uu____4717 = occurs uk t  in
      match uu____4717 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4746 =
                 let uu____4747 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4748 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4747 uu____4748
                  in
               FStar_Pervasives_Native.Some uu____4746)
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
            let uu____4837 = maximal_prefix bs_tail bs'_tail  in
            (match uu____4837 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____4881 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____4929  ->
             match uu____4929 with
             | (x,uu____4939) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____4952 = FStar_List.last bs  in
      match uu____4952 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____4970) ->
          let uu____4975 =
            FStar_Util.prefix_until
              (fun uu___323_4990  ->
                 match uu___323_4990 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____4992 -> false) g
             in
          (match uu____4975 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5005,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5041 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5041 with
        | (pfx,uu____5051) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5063 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5063 with
             | (uu____5070,src',wl1) ->
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
                 | uu____5170 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5171 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5225  ->
                  fun uu____5226  ->
                    match (uu____5225, uu____5226) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5307 =
                          let uu____5308 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5308
                           in
                        if uu____5307
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5333 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5333
                           then
                             let uu____5346 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5346)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5171 with | (isect,uu____5383) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5412 'Auu____5413 .
    (FStar_Syntax_Syntax.bv,'Auu____5412) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5413) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5470  ->
              fun uu____5471  ->
                match (uu____5470, uu____5471) with
                | ((a,uu____5489),(b,uu____5491)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5506 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5506) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5536  ->
           match uu____5536 with
           | (y,uu____5542) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5551 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5551) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
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
                   let uu____5681 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5681
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____5701 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____5744 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____5782 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5795 -> false
  
let string_of_option :
  'Auu____5802 .
    ('Auu____5802 -> Prims.string) ->
      'Auu____5802 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___324_5817  ->
      match uu___324_5817 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5823 = f x  in Prims.strcat "Some " uu____5823
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___325_5828  ->
    match uu___325_5828 with
    | MisMatch (d1,d2) ->
        let uu____5839 =
          let uu____5840 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5841 =
            let uu____5842 =
              let uu____5843 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5843 ")"  in
            Prims.strcat ") (" uu____5842  in
          Prims.strcat uu____5840 uu____5841  in
        Prims.strcat "MisMatch (" uu____5839
    | HeadMatch u ->
        let uu____5845 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____5845
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___326_5850  ->
    match uu___326_5850 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____5865 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
          let uu____5879 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5879 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____5890 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____5913 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5922 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5948 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5948
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5949 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5950 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5951 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5964 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5977 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6001) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6007,uu____6008) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6050) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6071;
             FStar_Syntax_Syntax.index = uu____6072;
             FStar_Syntax_Syntax.sort = t2;_},uu____6074)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6081 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6082 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6083 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6096 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6103 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6121 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6121
  
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
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____6148 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6148
            then FullMatch
            else
              (let uu____6150 =
                 let uu____6159 =
                   let uu____6162 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6162  in
                 let uu____6163 =
                   let uu____6166 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6166  in
                 (uu____6159, uu____6163)  in
               MisMatch uu____6150)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6172),FStar_Syntax_Syntax.Tm_uinst (g,uu____6174)) ->
            let uu____6183 = head_matches env f g  in
            FStar_All.pipe_right uu____6183 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6186 = FStar_Const.eq_const c d  in
            if uu____6186
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6193),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6195)) ->
            let uu____6228 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6228
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6235),FStar_Syntax_Syntax.Tm_refine (y,uu____6237)) ->
            let uu____6246 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6246 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6248),uu____6249) ->
            let uu____6254 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6254 head_match
        | (uu____6255,FStar_Syntax_Syntax.Tm_refine (x,uu____6257)) ->
            let uu____6262 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6262 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6263,FStar_Syntax_Syntax.Tm_type
           uu____6264) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6265,FStar_Syntax_Syntax.Tm_arrow uu____6266) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6292),FStar_Syntax_Syntax.Tm_app (head',uu____6294))
            ->
            let uu____6335 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6335 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6337),uu____6338) ->
            let uu____6359 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6359 head_match
        | (uu____6360,FStar_Syntax_Syntax.Tm_app (head1,uu____6362)) ->
            let uu____6383 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6383 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6384,FStar_Syntax_Syntax.Tm_let
           uu____6385) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6410,FStar_Syntax_Syntax.Tm_match uu____6411) ->
            HeadMatch true
        | uu____6456 ->
            let uu____6461 =
              let uu____6470 = delta_depth_of_term env t11  in
              let uu____6473 = delta_depth_of_term env t21  in
              (uu____6470, uu____6473)  in
            MisMatch uu____6461
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                        FStar_Pervasives_Native.tuple2
                        FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let maybe_inline t =
          let head1 = FStar_Syntax_Util.head_of t  in
          (let uu____6533 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6533
           then
             let uu____6534 = FStar_Syntax_Print.term_to_string t  in
             let uu____6535 = FStar_Syntax_Print.term_to_string head1  in
             FStar_Util.print2 "Head of %s is %s\n" uu____6534 uu____6535
           else ());
          (let uu____6537 =
             let uu____6538 = FStar_Syntax_Util.un_uinst head1  in
             uu____6538.FStar_Syntax_Syntax.n  in
           match uu____6537 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____6544 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant;
                   FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____6544 with
                | FStar_Pervasives_Native.None  ->
                    ((let uu____6558 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____6558
                      then
                        let uu____6559 =
                          FStar_Syntax_Print.term_to_string head1  in
                        FStar_Util.print1 "No definition found for %s\n"
                          uu____6559
                      else ());
                     FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.Some uu____6561 ->
                    let t' =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Normalize.Weak;
                        FStar_TypeChecker_Normalize.HNF;
                        FStar_TypeChecker_Normalize.Primops;
                        FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.Iota] env t
                       in
                    ((let uu____6572 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____6572
                      then
                        let uu____6573 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____6574 = FStar_Syntax_Print.term_to_string t'
                           in
                        FStar_Util.print2 "Inlined %s to %s\n" uu____6573
                          uu____6574
                      else ());
                     FStar_Pervasives_Native.Some t'))
           | uu____6576 -> FStar_Pervasives_Native.None)
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
          (let uu____6714 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6714
           then
             let uu____6715 = FStar_Syntax_Print.term_to_string t11  in
             let uu____6716 = FStar_Syntax_Print.term_to_string t21  in
             let uu____6717 = string_of_match_result r  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6715
               uu____6716 uu____6717
           else ());
          (let reduce_one_and_try_again d1 d2 =
             let d1_greater_than_d2 =
               FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
             let uu____6741 =
               if d1_greater_than_d2
               then
                 let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                     FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env t11
                    in
                 (t1', t21)
               else
                 (let t2' =
                    normalize_refinement
                      [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                      FStar_TypeChecker_Normalize.Weak;
                      FStar_TypeChecker_Normalize.HNF] env t21
                     in
                  (t11, t2'))
                in
             match uu____6741 with
             | (t12,t22) ->
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           let reduce_both_and_try_again d r1 =
             let uu____6786 = FStar_TypeChecker_Common.decr_delta_depth d  in
             match uu____6786 with
             | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
             | FStar_Pervasives_Native.Some d1 ->
                 let t12 =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                     FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env t11
                    in
                 let t22 =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                     FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env t21
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
                uu____6818),uu____6819)
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____6837 =
                    let uu____6846 = maybe_inline t11  in
                    let uu____6849 = maybe_inline t21  in
                    (uu____6846, uu____6849)  in
                  match uu____6837 with
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
               (uu____6886,FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level uu____6887))
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____6905 =
                    let uu____6914 = maybe_inline t11  in
                    let uu____6917 = maybe_inline t21  in
                    (uu____6914, uu____6917)  in
                  match uu____6905 with
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
               (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                d2)
               when d1 = d2 -> reduce_both_and_try_again d1 r
           | MisMatch
               (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                d2)
               -> reduce_one_and_try_again d1 d2
           | MisMatch uu____6966 -> fail1 n_delta r t11 t21
           | uu____6975 -> success n_delta r t11 t21)
           in
        let r = aux true (Prims.parse_int "0") t1 t2  in
        (let uu____6988 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelDelta")
            in
         if uu____6988
         then
           let uu____6989 = FStar_Syntax_Print.term_to_string t1  in
           let uu____6990 = FStar_Syntax_Print.term_to_string t2  in
           let uu____6991 =
             string_of_match_result (FStar_Pervasives_Native.fst r)  in
           let uu____6998 =
             if
               (FStar_Pervasives_Native.snd r) = FStar_Pervasives_Native.None
             then "None"
             else
               (let uu____7016 =
                  FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____7016
                  (fun uu____7050  ->
                     match uu____7050 with
                     | (t11,t21) ->
                         let uu____7057 =
                           FStar_Syntax_Print.term_to_string t11  in
                         let uu____7058 =
                           let uu____7059 =
                             FStar_Syntax_Print.term_to_string t21  in
                           Prims.strcat "; " uu____7059  in
                         Prims.strcat uu____7057 uu____7058))
              in
           FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
             uu____6989 uu____6990 uu____6991 uu____6998
         else ());
        r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7071 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7071 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___327_7084  ->
    match uu___327_7084 with
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
      let uu___348_7121 = p  in
      let uu____7124 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7125 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___348_7121.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7124;
        FStar_TypeChecker_Common.relation =
          (uu___348_7121.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7125;
        FStar_TypeChecker_Common.element =
          (uu___348_7121.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___348_7121.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___348_7121.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___348_7121.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___348_7121.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___348_7121.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7139 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7139
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7144 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7166 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7166 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7174 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7174 with
           | (lh,lhs_args) ->
               let uu____7215 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7215 with
                | (rh,rhs_args) ->
                    let uu____7256 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7269,FStar_Syntax_Syntax.Tm_uvar uu____7270)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7347 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7370,uu____7371)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7386,FStar_Syntax_Syntax.Tm_uvar uu____7387)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7402,FStar_Syntax_Syntax.Tm_arrow uu____7403)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___349_7431 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___349_7431.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___349_7431.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___349_7431.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___349_7431.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___349_7431.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___349_7431.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___349_7431.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___349_7431.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___349_7431.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7434,FStar_Syntax_Syntax.Tm_type uu____7435)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___349_7451 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___349_7451.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___349_7451.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___349_7451.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___349_7451.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___349_7451.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___349_7451.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___349_7451.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___349_7451.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___349_7451.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7454,FStar_Syntax_Syntax.Tm_uvar uu____7455)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___349_7471 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___349_7471.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___349_7471.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___349_7471.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___349_7471.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___349_7471.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___349_7471.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___349_7471.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___349_7471.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___349_7471.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7474,FStar_Syntax_Syntax.Tm_uvar uu____7475)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7490,uu____7491)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7506,FStar_Syntax_Syntax.Tm_uvar uu____7507)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7522,uu____7523) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7256 with
                     | (rank,tp1) ->
                         let uu____7536 =
                           FStar_All.pipe_right
                             (let uu___350_7540 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___350_7540.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___350_7540.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___350_7540.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___350_7540.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___350_7540.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___350_7540.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___350_7540.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___350_7540.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___350_7540.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____7536))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7546 =
            FStar_All.pipe_right
              (let uu___351_7550 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___351_7550.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___351_7550.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___351_7550.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___351_7550.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___351_7550.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___351_7550.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___351_7550.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___351_7550.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___351_7550.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7546)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____7611 probs =
      match uu____7611 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____7692 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____7713 = rank wl.tcenv hd1  in
               (match uu____7713 with
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
                      (let uu____7772 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7776 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____7776)
                          in
                       if uu____7772
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
          let uu____7844 = FStar_Syntax_Util.head_and_args t  in
          match uu____7844 with
          | (hd1,uu____7860) ->
              let uu____7881 =
                let uu____7882 = FStar_Syntax_Subst.compress hd1  in
                uu____7882.FStar_Syntax_Syntax.n  in
              (match uu____7881 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____7886) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____7916  ->
                           match uu____7916 with
                           | (y,uu____7922) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____7936  ->
                                       match uu____7936 with
                                       | (x,uu____7942) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____7943 -> false)
           in
        let uu____7944 = rank tcenv p  in
        match uu____7944 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____7951 -> true
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
    match projectee with | UDeferred _0 -> true | uu____7978 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____7992 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8006 -> false
  
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
                        let uu____8058 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8058 with
                        | (k,uu____8064) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8074 -> false)))
            | uu____8075 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8127 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8133 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8133 = (Prims.parse_int "0")))
                           in
                        if uu____8127 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8149 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8155 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8155 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8149)
               in
            let uu____8156 = filter1 u12  in
            let uu____8159 = filter1 u22  in (uu____8156, uu____8159)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8188 = filter_out_common_univs us1 us2  in
                (match uu____8188 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8247 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8247 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8250 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8260 =
                          let uu____8261 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8262 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8261
                            uu____8262
                           in
                        UFailed uu____8260))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8286 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8286 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8312 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8312 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8315 ->
                let uu____8320 =
                  let uu____8321 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8322 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8321
                    uu____8322 msg
                   in
                UFailed uu____8320
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8323,uu____8324) ->
              let uu____8325 =
                let uu____8326 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8327 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8326 uu____8327
                 in
              failwith uu____8325
          | (FStar_Syntax_Syntax.U_unknown ,uu____8328) ->
              let uu____8329 =
                let uu____8330 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8331 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8330 uu____8331
                 in
              failwith uu____8329
          | (uu____8332,FStar_Syntax_Syntax.U_bvar uu____8333) ->
              let uu____8334 =
                let uu____8335 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8336 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8335 uu____8336
                 in
              failwith uu____8334
          | (uu____8337,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8338 =
                let uu____8339 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8340 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8339 uu____8340
                 in
              failwith uu____8338
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8364 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8364
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8378 = occurs_univ v1 u3  in
              if uu____8378
              then
                let uu____8379 =
                  let uu____8380 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8381 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8380 uu____8381
                   in
                try_umax_components u11 u21 uu____8379
              else
                (let uu____8383 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8383)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8395 = occurs_univ v1 u3  in
              if uu____8395
              then
                let uu____8396 =
                  let uu____8397 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8398 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8397 uu____8398
                   in
                try_umax_components u11 u21 uu____8396
              else
                (let uu____8400 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8400)
          | (FStar_Syntax_Syntax.U_max uu____8401,uu____8402) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8408 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8408
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8410,FStar_Syntax_Syntax.U_max uu____8411) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8417 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8417
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8419,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8420,FStar_Syntax_Syntax.U_name
             uu____8421) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8422) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8423) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8424,FStar_Syntax_Syntax.U_succ
             uu____8425) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8426,FStar_Syntax_Syntax.U_zero
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
      let uu____8526 = bc1  in
      match uu____8526 with
      | (bs1,mk_cod1) ->
          let uu____8570 = bc2  in
          (match uu____8570 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____8681 = aux xs ys  in
                     (match uu____8681 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____8764 =
                       let uu____8771 = mk_cod1 xs  in ([], uu____8771)  in
                     let uu____8774 =
                       let uu____8781 = mk_cod2 ys  in ([], uu____8781)  in
                     (uu____8764, uu____8774)
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
                  let uu____8849 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____8849 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____8852 =
                    let uu____8853 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____8853 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____8852
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____8858 = has_type_guard t1 t2  in (uu____8858, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____8859 = has_type_guard t2 t1  in (uu____8859, wl)
  
let is_flex_pat :
  'Auu____8868 'Auu____8869 'Auu____8870 .
    ('Auu____8868,'Auu____8869,'Auu____8870 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___328_8883  ->
    match uu___328_8883 with
    | (uu____8892,uu____8893,[]) -> true
    | uu____8896 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8927 = f  in
      match uu____8927 with
      | (uu____8934,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8935;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8936;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8939;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8940;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8941;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____8993  ->
                 match uu____8993 with
                 | (y,uu____8999) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9121 =
                  let uu____9134 =
                    let uu____9137 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9137  in
                  ((FStar_List.rev pat_binders), uu____9134)  in
                FStar_Pervasives_Native.Some uu____9121
            | (uu____9164,[]) ->
                let uu____9187 =
                  let uu____9200 =
                    let uu____9203 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9203  in
                  ((FStar_List.rev pat_binders), uu____9200)  in
                FStar_Pervasives_Native.Some uu____9187
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9268 =
                  let uu____9269 = FStar_Syntax_Subst.compress a  in
                  uu____9269.FStar_Syntax_Syntax.n  in
                (match uu____9268 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9287 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9287
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___352_9308 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___352_9308.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___352_9308.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9312 =
                            let uu____9313 =
                              let uu____9320 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9320)  in
                            FStar_Syntax_Syntax.NT uu____9313  in
                          [uu____9312]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___353_9332 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___353_9332.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___353_9332.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9333 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9361 =
                  let uu____9374 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9374  in
                (match uu____9361 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9437 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9464 ->
               let uu____9465 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9465 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9741 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____9741
       then
         let uu____9742 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9742
       else ());
      (let uu____9744 = next_prob probs  in
       match uu____9744 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___354_9771 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___354_9771.wl_deferred);
               ctr = (uu___354_9771.ctr);
               defer_ok = (uu___354_9771.defer_ok);
               smt_ok = (uu___354_9771.smt_ok);
               tcenv = (uu___354_9771.tcenv);
               wl_implicits = (uu___354_9771.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____9779 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____9779
                 then
                   let uu____9780 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____9780
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
                           (let uu___355_9785 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___355_9785.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___355_9785.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___355_9785.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___355_9785.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___355_9785.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___355_9785.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___355_9785.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___355_9785.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___355_9785.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9807 ->
                let uu____9816 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9875  ->
                          match uu____9875 with
                          | (c,uu____9883,uu____9884) -> c < probs.ctr))
                   in
                (match uu____9816 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9925 =
                            let uu____9930 =
                              FStar_List.map
                                (fun uu____9945  ->
                                   match uu____9945 with
                                   | (uu____9956,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9930, (probs.wl_implicits))  in
                          Success uu____9925
                      | uu____9959 ->
                          let uu____9968 =
                            let uu___356_9969 = probs  in
                            let uu____9970 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9989  ->
                                      match uu____9989 with
                                      | (uu____9996,uu____9997,y) -> y))
                               in
                            {
                              attempting = uu____9970;
                              wl_deferred = rest;
                              ctr = (uu___356_9969.ctr);
                              defer_ok = (uu___356_9969.defer_ok);
                              smt_ok = (uu___356_9969.smt_ok);
                              tcenv = (uu___356_9969.tcenv);
                              wl_implicits = (uu___356_9969.wl_implicits)
                            }  in
                          solve env uu____9968))))

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
            let uu____10004 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10004 with
            | USolved wl1 ->
                let uu____10006 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10006
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
                  let uu____10058 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10058 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10061 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10073;
                  FStar_Syntax_Syntax.vars = uu____10074;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10077;
                  FStar_Syntax_Syntax.vars = uu____10078;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10090,uu____10091) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10098,FStar_Syntax_Syntax.Tm_uinst uu____10099) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10106 -> USolved wl

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
            ((let uu____10116 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10116
              then
                let uu____10117 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10117 msg
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
               let uu____10203 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10203 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10256 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10256
                then
                  let uu____10257 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10258 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10257 uu____10258
                else ());
               (let uu____10260 = head_matches_delta env1 t1 t2  in
                match uu____10260 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10305 = eq_prob t1 t2 wl2  in
                         (match uu____10305 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____10326 ->
                         let uu____10335 = eq_prob t1 t2 wl2  in
                         (match uu____10335 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____10384 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____10399 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____10400 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____10399, uu____10400)
                           | FStar_Pervasives_Native.None  ->
                               let uu____10405 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____10406 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____10405, uu____10406)
                            in
                         (match uu____10384 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____10437 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____10437 with
                                | (t1_hd,t1_args) ->
                                    let uu____10476 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____10476 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____10530 =
                                              let uu____10537 =
                                                let uu____10546 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____10546 :: t1_args  in
                                              let uu____10559 =
                                                let uu____10566 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____10566 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____10607  ->
                                                   fun uu____10608  ->
                                                     fun uu____10609  ->
                                                       match (uu____10607,
                                                               uu____10608,
                                                               uu____10609)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____10651),
                                                          (a2,uu____10653))
                                                           ->
                                                           let uu____10678 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____10678
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____10537
                                                uu____10559
                                               in
                                            match uu____10530 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___357_10704 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___357_10704.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___357_10704.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____10712 =
                                                  solve env1 wl'  in
                                                (match uu____10712 with
                                                 | Success (uu____10715,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___358_10719
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___358_10719.attempting);
                                                            wl_deferred =
                                                              (uu___358_10719.wl_deferred);
                                                            ctr =
                                                              (uu___358_10719.ctr);
                                                            defer_ok =
                                                              (uu___358_10719.defer_ok);
                                                            smt_ok =
                                                              (uu___358_10719.smt_ok);
                                                            tcenv =
                                                              (uu___358_10719.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____10720 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____10752 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____10752 with
                                | (t1_base,p1_opt) ->
                                    let uu____10799 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____10799 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____10909 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____10909
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
                                               let uu____10957 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____10957
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
                                               let uu____10987 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____10987
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
                                               let uu____11017 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11017
                                           | uu____11020 -> t_base  in
                                         let uu____11037 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11037 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11051 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11051, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11058 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11058 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11105 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11105 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11152 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11152
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
                              let uu____11176 = combine t11 t21 wl2  in
                              (match uu____11176 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11209 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11209
                                     then
                                       let uu____11210 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11210
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11249 ts1 =
               match uu____11249 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____11312 = pairwise out t wl2  in
                        (match uu____11312 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____11348 =
               let uu____11359 = FStar_List.hd ts  in (uu____11359, [], wl1)
                in
             let uu____11368 = FStar_List.tl ts  in
             aux uu____11348 uu____11368  in
           let uu____11375 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____11375 with
           | (this_flex,this_rigid) ->
               let uu____11399 =
                 let uu____11400 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____11400.FStar_Syntax_Syntax.n  in
               (match uu____11399 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____11421 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____11421
                    then
                      let uu____11422 = destruct_flex_t this_flex wl  in
                      (match uu____11422 with
                       | (flex,wl1) ->
                           let uu____11429 = quasi_pattern env flex  in
                           (match uu____11429 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____11447 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____11447
                                  then
                                    let uu____11448 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____11448
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____11451 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___359_11454 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___359_11454.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___359_11454.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___359_11454.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___359_11454.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___359_11454.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___359_11454.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___359_11454.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___359_11454.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___359_11454.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____11451)
                | uu____11455 ->
                    ((let uu____11457 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11457
                      then
                        let uu____11458 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____11458
                      else ());
                     (let uu____11460 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____11460 with
                      | (u,_args) ->
                          let uu____11497 =
                            let uu____11498 = FStar_Syntax_Subst.compress u
                               in
                            uu____11498.FStar_Syntax_Syntax.n  in
                          (match uu____11497 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____11525 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____11525 with
                                 | (u',uu____11541) ->
                                     let uu____11562 =
                                       let uu____11563 = whnf env u'  in
                                       uu____11563.FStar_Syntax_Syntax.n  in
                                     (match uu____11562 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____11584 -> false)
                                  in
                               let uu____11585 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___329_11608  ->
                                         match uu___329_11608 with
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
                                              | uu____11617 -> false)
                                         | uu____11620 -> false))
                                  in
                               (match uu____11585 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____11634 = whnf env this_rigid
                                         in
                                      let uu____11635 =
                                        FStar_List.collect
                                          (fun uu___330_11641  ->
                                             match uu___330_11641 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____11647 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____11647]
                                             | uu____11649 -> [])
                                          bounds_probs
                                         in
                                      uu____11634 :: uu____11635  in
                                    let uu____11650 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____11650 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____11681 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____11696 =
                                               let uu____11697 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____11697.FStar_Syntax_Syntax.n
                                                in
                                             match uu____11696 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____11709 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____11709)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____11718 -> bound  in
                                           let uu____11719 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____11719)  in
                                         (match uu____11681 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____11748 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____11748
                                                then
                                                  let wl'1 =
                                                    let uu___360_11750 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___360_11750.wl_deferred);
                                                      ctr =
                                                        (uu___360_11750.ctr);
                                                      defer_ok =
                                                        (uu___360_11750.defer_ok);
                                                      smt_ok =
                                                        (uu___360_11750.smt_ok);
                                                      tcenv =
                                                        (uu___360_11750.tcenv);
                                                      wl_implicits =
                                                        (uu___360_11750.wl_implicits)
                                                    }  in
                                                  let uu____11751 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____11751
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11754 =
                                                  solve_t env eq_prob
                                                    (let uu___361_11756 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___361_11756.wl_deferred);
                                                       ctr =
                                                         (uu___361_11756.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___361_11756.smt_ok);
                                                       tcenv =
                                                         (uu___361_11756.tcenv);
                                                       wl_implicits =
                                                         (uu___361_11756.wl_implicits)
                                                     })
                                                   in
                                                match uu____11754 with
                                                | Success uu____11757 ->
                                                    let wl2 =
                                                      let uu___362_11763 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___362_11763.wl_deferred);
                                                        ctr =
                                                          (uu___362_11763.ctr);
                                                        defer_ok =
                                                          (uu___362_11763.defer_ok);
                                                        smt_ok =
                                                          (uu___362_11763.smt_ok);
                                                        tcenv =
                                                          (uu___362_11763.tcenv);
                                                        wl_implicits =
                                                          (uu___362_11763.wl_implicits)
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
                                                    let uu____11778 =
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
                                                    ((let uu____11789 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____11789
                                                      then
                                                        let uu____11790 =
                                                          let uu____11791 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____11791
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____11790
                                                      else ());
                                                     (let uu____11797 =
                                                        let uu____11812 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____11812)
                                                         in
                                                      match uu____11797 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____11834))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____11860 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____11860
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
                                                                  let uu____11877
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____11877))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____11902 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____11902
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
                                                                    let uu____11920
                                                                    =
                                                                    let uu____11925
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11925
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____11920
                                                                    [] wl2
                                                                     in
                                                                  let uu____11930
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____11930))))
                                                      | uu____11931 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____11946 when flip ->
                               let uu____11947 =
                                 let uu____11948 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____11949 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____11948 uu____11949
                                  in
                               failwith uu____11947
                           | uu____11950 ->
                               let uu____11951 =
                                 let uu____11952 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____11953 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____11952 uu____11953
                                  in
                               failwith uu____11951)))))

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
                      (fun uu____11981  ->
                         match uu____11981 with
                         | (x,i) ->
                             let uu____11992 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____11992, i)) bs_lhs
                     in
                  let uu____11993 = lhs  in
                  match uu____11993 with
                  | (uu____11994,u_lhs,uu____11996) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12089 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12099 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12099, univ)
                             in
                          match uu____12089 with
                          | (k,univ) ->
                              let uu____12106 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12106 with
                               | (uu____12121,u,wl3) ->
                                   let uu____12124 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12124, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12150 =
                              let uu____12161 =
                                let uu____12170 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12170 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12213  ->
                                   fun uu____12214  ->
                                     match (uu____12213, uu____12214) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12293 =
                                           let uu____12300 =
                                             let uu____12303 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12303
                                              in
                                           copy_uvar u_lhs [] uu____12300 wl2
                                            in
                                         (match uu____12293 with
                                          | (uu____12328,t_a,wl3) ->
                                              let uu____12331 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____12331 with
                                               | (uu____12348,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12161
                                ([], wl1)
                               in
                            (match uu____12150 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___363_12390 = ct  in
                                   let uu____12391 =
                                     let uu____12394 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12394
                                      in
                                   let uu____12403 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___363_12390.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___363_12390.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12391;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12403;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___363_12390.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___364_12417 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___364_12417.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___364_12417.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12420 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12420 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12474 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12474 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12485 =
                                          let uu____12490 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12490)  in
                                        TERM uu____12485  in
                                      let uu____12491 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12491 with
                                       | (sub_prob,wl3) ->
                                           let uu____12502 =
                                             let uu____12503 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12503
                                              in
                                           solve env uu____12502))
                             | (x,imp)::formals2 ->
                                 let uu____12517 =
                                   let uu____12524 =
                                     let uu____12527 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____12527
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____12524 wl1
                                    in
                                 (match uu____12517 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____12546 =
                                          let uu____12549 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12549
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12546 u_x
                                         in
                                      let uu____12550 =
                                        let uu____12553 =
                                          let uu____12556 =
                                            let uu____12557 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12557, imp)  in
                                          [uu____12556]  in
                                        FStar_List.append bs_terms
                                          uu____12553
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12550 formals2 wl2)
                              in
                           let uu____12574 = occurs_check u_lhs arrow1  in
                           (match uu____12574 with
                            | (uu____12585,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____12596 =
                                    let uu____12597 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____12597
                                     in
                                  giveup_or_defer env orig wl uu____12596
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
              (let uu____12624 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12624
               then
                 let uu____12625 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12626 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12625 (rel_to_string (p_rel orig)) uu____12626
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____12731 = rhs wl1 scope env1 subst1  in
                     (match uu____12731 with
                      | (rhs_prob,wl2) ->
                          ((let uu____12751 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____12751
                            then
                              let uu____12752 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____12752
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___365_12806 = hd1  in
                       let uu____12807 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___365_12806.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___365_12806.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12807
                       }  in
                     let hd21 =
                       let uu___366_12811 = hd2  in
                       let uu____12812 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___366_12811.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___366_12811.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12812
                       }  in
                     let uu____12815 =
                       let uu____12820 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____12820
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____12815 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____12839 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____12839
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____12843 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____12843 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____12898 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____12898
                                  in
                               ((let uu____12910 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____12910
                                 then
                                   let uu____12911 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____12912 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____12911
                                     uu____12912
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____12939 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____12968 = aux wl [] env [] bs1 bs2  in
               match uu____12968 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13015 = attempt sub_probs wl2  in
                   solve env uu____13015)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13020 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13020 wl)

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
              let uu____13034 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13034 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13064 = lhs1  in
              match uu____13064 with
              | (uu____13067,ctx_u,uu____13069) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13075 ->
                        let uu____13076 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13076 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13123 = quasi_pattern env1 lhs1  in
              match uu____13123 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13153) ->
                  let uu____13158 = lhs1  in
                  (match uu____13158 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13172 = occurs_check ctx_u rhs1  in
                       (match uu____13172 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13214 =
                                let uu____13221 =
                                  let uu____13222 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13222
                                   in
                                FStar_Util.Inl uu____13221  in
                              (uu____13214, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13242 =
                                 let uu____13243 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13243  in
                               if uu____13242
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13263 =
                                    let uu____13270 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13270  in
                                  let uu____13275 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13263, uu____13275)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13337  ->
                     match uu____13337 with
                     | (x,i) ->
                         let uu____13348 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13348, i)) bs_lhs
                 in
              let uu____13349 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13349 with
              | (rhs_hd,args) ->
                  let uu____13386 = FStar_Util.prefix args  in
                  (match uu____13386 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13444 = lhs1  in
                       (match uu____13444 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13448 =
                              let uu____13459 =
                                let uu____13466 =
                                  let uu____13469 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13469
                                   in
                                copy_uvar u_lhs [] uu____13466 wl1  in
                              match uu____13459 with
                              | (uu____13494,t_last_arg,wl2) ->
                                  let uu____13497 =
                                    let uu____13504 =
                                      let uu____13505 =
                                        let uu____13512 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____13512]  in
                                      FStar_List.append bs_lhs uu____13505
                                       in
                                    copy_uvar u_lhs uu____13504 t_res_lhs wl2
                                     in
                                  (match uu____13497 with
                                   | (uu____13539,lhs',wl3) ->
                                       let uu____13542 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____13542 with
                                        | (uu____13559,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13448 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13580 =
                                     let uu____13581 =
                                       let uu____13586 =
                                         let uu____13587 =
                                           let uu____13590 =
                                             let uu____13595 =
                                               let uu____13596 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13596]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13595
                                              in
                                           uu____13590
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13587
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13586)  in
                                     TERM uu____13581  in
                                   [uu____13580]  in
                                 let uu____13617 =
                                   let uu____13624 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____13624 with
                                   | (p1,wl3) ->
                                       let uu____13641 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____13641 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13617 with
                                  | (sub_probs,wl3) ->
                                      let uu____13668 =
                                        let uu____13669 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____13669  in
                                      solve env1 uu____13668))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____13702 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____13702 with
                | (uu____13717,args) ->
                    (match args with | [] -> false | uu____13745 -> true)
                 in
              let is_arrow rhs2 =
                let uu____13760 =
                  let uu____13761 = FStar_Syntax_Subst.compress rhs2  in
                  uu____13761.FStar_Syntax_Syntax.n  in
                match uu____13760 with
                | FStar_Syntax_Syntax.Tm_arrow uu____13764 -> true
                | uu____13777 -> false  in
              let uu____13778 = quasi_pattern env1 lhs1  in
              match uu____13778 with
              | FStar_Pervasives_Native.None  ->
                  let uu____13789 =
                    let uu____13790 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____13790
                     in
                  giveup_or_defer env1 orig1 wl1 uu____13789
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____13797 = is_app rhs1  in
                  if uu____13797
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____13799 = is_arrow rhs1  in
                     if uu____13799
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____13801 =
                          let uu____13802 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____13802
                           in
                        giveup_or_defer env1 orig1 wl1 uu____13801))
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
                let uu____13805 = lhs  in
                (match uu____13805 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____13809 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____13809 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____13824 =
                              let uu____13827 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____13827
                               in
                            FStar_All.pipe_right uu____13824
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____13842 = occurs_check ctx_uv rhs1  in
                          (match uu____13842 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____13864 =
                                   let uu____13865 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____13865
                                    in
                                 giveup_or_defer env orig wl uu____13864
                               else
                                 (let uu____13867 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____13867
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____13872 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____13872
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____13874 =
                                         let uu____13875 =
                                           names_to_string1 fvs2  in
                                         let uu____13876 =
                                           names_to_string1 fvs1  in
                                         let uu____13877 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____13875 uu____13876
                                           uu____13877
                                          in
                                       giveup_or_defer env orig wl
                                         uu____13874)
                                    else first_order orig env wl lhs rhs1))
                      | uu____13883 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____13887 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____13887 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____13910 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____13910
                             | (FStar_Util.Inl msg,uu____13912) ->
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
                  (let uu____13941 =
                     let uu____13958 = quasi_pattern env lhs  in
                     let uu____13965 = quasi_pattern env rhs  in
                     (uu____13958, uu____13965)  in
                   match uu____13941 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14008 = lhs  in
                       (match uu____14008 with
                        | ({ FStar_Syntax_Syntax.n = uu____14009;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14011;_},u_lhs,uu____14013)
                            ->
                            let uu____14016 = rhs  in
                            (match uu____14016 with
                             | (uu____14017,u_rhs,uu____14019) ->
                                 let uu____14020 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14020
                                 then
                                   let uu____14021 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14021
                                 else
                                   (let uu____14023 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14023 with
                                    | (sub_prob,wl1) ->
                                        let uu____14034 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14034 with
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
                                             let uu____14062 =
                                               let uu____14069 =
                                                 let uu____14072 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14072
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi:"
                                                    (Prims.strcat "\tlhs="
                                                       (Prims.strcat
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                          (Prims.strcat
                                                             "\trhs="
                                                             u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                                 wl1 range gamma_w ctx_w
                                                 uu____14069
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14062 with
                                              | (uu____14075,w,wl2) ->
                                                  let w_app =
                                                    let uu____14081 =
                                                      let uu____14086 =
                                                        FStar_List.map
                                                          (fun uu____14095 
                                                             ->
                                                             match uu____14095
                                                             with
                                                             | (z,uu____14101)
                                                                 ->
                                                                 let uu____14102
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14102)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14086
                                                       in
                                                    uu____14081
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14106 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14106
                                                    then
                                                      let uu____14107 =
                                                        let uu____14110 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14111 =
                                                          let uu____14114 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14115 =
                                                            let uu____14118 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14119 =
                                                              let uu____14122
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14127
                                                                =
                                                                let uu____14130
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14135
                                                                  =
                                                                  let uu____14138
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14138]
                                                                   in
                                                                uu____14130
                                                                  ::
                                                                  uu____14135
                                                                 in
                                                              uu____14122 ::
                                                                uu____14127
                                                               in
                                                            uu____14118 ::
                                                              uu____14119
                                                             in
                                                          uu____14114 ::
                                                            uu____14115
                                                           in
                                                        uu____14110 ::
                                                          uu____14111
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14107
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14144 =
                                                          let uu____14149 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14149)
                                                           in
                                                        TERM uu____14144  in
                                                      let uu____14150 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14150
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14155 =
                                                             let uu____14160
                                                               =
                                                               FStar_Syntax_Util.abs
                                                                 binders_rhs
                                                                 w_app
                                                                 (FStar_Pervasives_Native.Some
                                                                    (
                                                                    FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                                in
                                                             (u_rhs,
                                                               uu____14160)
                                                              in
                                                           TERM uu____14155
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14161 =
                                                      let uu____14162 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14162
                                                       in
                                                    solve env uu____14161)))))))
                   | uu____14163 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14227 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14227
            then
              let uu____14228 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14229 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14230 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14231 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14228 uu____14229 uu____14230 uu____14231
            else ());
           (let uu____14234 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14234 with
            | (head1,args1) ->
                let uu____14271 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14271 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____14325 =
                         let uu____14326 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14327 = args_to_string args1  in
                         let uu____14328 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____14329 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____14326 uu____14327 uu____14328 uu____14329
                          in
                       giveup env1 uu____14325 orig
                     else
                       (let uu____14331 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____14337 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____14337 = FStar_Syntax_Util.Equal)
                           in
                        if uu____14331
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___367_14339 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___367_14339.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___367_14339.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___367_14339.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___367_14339.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___367_14339.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___367_14339.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___367_14339.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___367_14339.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____14341 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____14341 with
                              | USolved wl2 ->
                                  let uu____14343 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____14343
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____14347 = base_and_refinement env1 t1  in
                           match uu____14347 with
                           | (base1,refinement1) ->
                               let uu____14372 = base_and_refinement env1 t2
                                  in
                               (match uu____14372 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         if need_unif
                                         then
                                           let argp =
                                             FStar_List.zip
                                               ((head1,
                                                  FStar_Pervasives_Native.None)
                                               :: args1)
                                               ((head2,
                                                  FStar_Pervasives_Native.None)
                                               :: args2)
                                              in
                                           let uu____14476 =
                                             FStar_List.fold_right
                                               (fun uu____14512  ->
                                                  fun uu____14513  ->
                                                    match (uu____14512,
                                                            uu____14513)
                                                    with
                                                    | (((a1,uu____14557),
                                                        (a2,uu____14559)),
                                                       (probs,wl2)) ->
                                                        let uu____14592 =
                                                          let uu____14599 =
                                                            p_scope orig  in
                                                          mk_problem wl2
                                                            uu____14599 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____14592
                                                         with
                                                         | (prob',wl3) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl3)))
                                               argp ([], wl1)
                                              in
                                           (match uu____14476 with
                                            | (subprobs,wl2) ->
                                                ((let uu____14629 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____14629
                                                  then
                                                    let uu____14630 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____14630
                                                  else ());
                                                 (let formula =
                                                    let uu____14635 =
                                                      FStar_List.map
                                                        (fun p  -> p_guard p)
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____14635
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  let uu____14643 =
                                                    attempt subprobs wl3  in
                                                  solve env1 uu____14643)))
                                         else
                                           (let uu____14645 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____14645 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let uu____14649 =
                                                  FStar_List.fold_right2
                                                    (fun uu____14682  ->
                                                       fun uu____14683  ->
                                                         fun uu____14684  ->
                                                           match (uu____14682,
                                                                   uu____14683,
                                                                   uu____14684)
                                                           with
                                                           | ((a,uu____14720),
                                                              (a',uu____14722),
                                                              (subprobs,wl3))
                                                               ->
                                                               let uu____14743
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 []
                                                                   orig a
                                                                   FStar_TypeChecker_Common.EQ
                                                                   a'
                                                                   FStar_Pervasives_Native.None
                                                                   "index"
                                                                  in
                                                               (match uu____14743
                                                                with
                                                                | (p,wl4) ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                    args1 args2 ([], wl2)
                                                   in
                                                (match uu____14649 with
                                                 | (subprobs,wl3) ->
                                                     ((let uu____14771 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           (FStar_Options.Other
                                                              "Rel")
                                                          in
                                                       if uu____14771
                                                       then
                                                         let uu____14772 =
                                                           FStar_Syntax_Print.list_to_string
                                                             (prob_to_string
                                                                env1)
                                                             subprobs
                                                            in
                                                         FStar_Util.print1
                                                           "Adding subproblems for arguments: %s\n"
                                                           uu____14772
                                                       else ());
                                                      FStar_List.iter
                                                        (def_check_prob
                                                           "solve_t' subprobs")
                                                        subprobs;
                                                      (let formula =
                                                         let uu____14778 =
                                                           FStar_List.map
                                                             p_guard subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____14778
                                                          in
                                                       let wl4 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl3
                                                          in
                                                       let uu____14786 =
                                                         attempt subprobs wl4
                                                          in
                                                       solve env1 uu____14786))))
                                     | uu____14787 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___368_14823 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___368_14823.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___368_14823.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___368_14823.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___368_14823.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___368_14823.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___368_14823.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___368_14823.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___368_14823.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____14898 = destruct_flex_t scrutinee wl1  in
             match uu____14898 with
             | ((_t,uv,_args),wl2) ->
                 let tc_annot env2 t =
                   let uu____14924 =
                     env2.FStar_TypeChecker_Env.type_of
                       (let uu___369_14932 = env2  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___369_14932.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___369_14932.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___369_14932.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___369_14932.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___369_14932.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___369_14932.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___369_14932.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___369_14932.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___369_14932.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___369_14932.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___369_14932.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___369_14932.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___369_14932.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___369_14932.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___369_14932.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___369_14932.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___369_14932.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___369_14932.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___369_14932.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___369_14932.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___369_14932.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___369_14932.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___369_14932.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___369_14932.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___369_14932.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___369_14932.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___369_14932.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___369_14932.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___369_14932.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts = true;
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___369_14932.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___369_14932.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___369_14932.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___369_14932.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___369_14932.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___369_14932.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___369_14932.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___369_14932.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___369_14932.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___369_14932.FStar_TypeChecker_Env.dep_graph)
                        }) t
                      in
                   match uu____14924 with | (t1,uu____14938,g) -> (t1, g)  in
                 let uu____14940 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p
                     tc_annot
                    in
                 (match uu____14940 with
                  | (xs,pat_term,uu____14955,uu____14956) ->
                      let uu____14961 =
                        FStar_List.fold_left
                          (fun uu____14984  ->
                             fun x  ->
                               match uu____14984 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____15005 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____15005 with
                                    | (uu____15022,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____14961 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____15043 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____15043 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___370_15059 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___370_15059.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    tcenv = (uu___370_15059.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____15067 = solve env1 wl'  in
                                (match uu____15067 with
                                 | Success (uu____15070,imps) ->
                                     let wl'1 =
                                       let uu___371_15073 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___371_15073.wl_deferred);
                                         ctr = (uu___371_15073.ctr);
                                         defer_ok = (uu___371_15073.defer_ok);
                                         smt_ok = (uu___371_15073.smt_ok);
                                         tcenv = (uu___371_15073.tcenv);
                                         wl_implicits =
                                           (uu___371_15073.wl_implicits)
                                       }  in
                                     let uu____15074 = solve env1 wl'1  in
                                     (match uu____15074 with
                                      | Success (uu____15077,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___372_15081 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___372_15081.attempting);
                                                 wl_deferred =
                                                   (uu___372_15081.wl_deferred);
                                                 ctr = (uu___372_15081.ctr);
                                                 defer_ok =
                                                   (uu___372_15081.defer_ok);
                                                 smt_ok =
                                                   (uu___372_15081.smt_ok);
                                                 tcenv =
                                                   (uu___372_15081.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____15082 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____15088 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____15109 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____15109
                 then
                   let uu____15110 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____15111 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____15110 uu____15111
                 else ());
                (let uu____15113 =
                   let uu____15134 =
                     let uu____15143 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____15143)  in
                   let uu____15150 =
                     let uu____15159 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____15159)  in
                   (uu____15134, uu____15150)  in
                 match uu____15113 with
                 | ((uu____15188,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____15191;
                                   FStar_Syntax_Syntax.vars = uu____15192;_}),
                    (s,t)) ->
                     let uu____15263 =
                       let uu____15264 = is_flex scrutinee  in
                       Prims.op_Negation uu____15264  in
                     if uu____15263
                     then
                       ((let uu____15272 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____15272
                         then
                           let uu____15273 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____15273
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____15285 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15285
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____15291 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15291
                           then
                             let uu____15292 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____15293 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____15292 uu____15293
                           else ());
                          (let pat_discriminates uu___331_15314 =
                             match uu___331_15314 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____15329;
                                  FStar_Syntax_Syntax.p = uu____15330;_},FStar_Pervasives_Native.None
                                ,uu____15331) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____15344;
                                  FStar_Syntax_Syntax.p = uu____15345;_},FStar_Pervasives_Native.None
                                ,uu____15346) -> true
                             | uu____15371 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____15471 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____15471 with
                                       | (uu____15472,uu____15473,t') ->
                                           let uu____15491 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____15491 with
                                            | (FullMatch ,uu____15502) ->
                                                true
                                            | (HeadMatch
                                               uu____15515,uu____15516) ->
                                                true
                                            | uu____15529 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____15562 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15562
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____15567 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____15567 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____15655,uu____15656) ->
                                       branches1
                                   | uu____15801 -> branches  in
                                 let uu____15856 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____15865 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____15865 with
                                        | (p,uu____15869,uu____15870) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____15856))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____15926 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____15926 with
                                | (p,uu____15934,e) ->
                                    ((let uu____15953 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____15953
                                      then
                                        let uu____15954 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____15955 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____15954 uu____15955
                                      else ());
                                     (let uu____15957 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____15957)))))
                 | ((s,t),(uu____15972,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____15975;
                                         FStar_Syntax_Syntax.vars =
                                           uu____15976;_}))
                     ->
                     let uu____16045 =
                       let uu____16046 = is_flex scrutinee  in
                       Prims.op_Negation uu____16046  in
                     if uu____16045
                     then
                       ((let uu____16054 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16054
                         then
                           let uu____16055 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16055
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16067 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16067
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16073 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16073
                           then
                             let uu____16074 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16075 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16074 uu____16075
                           else ());
                          (let pat_discriminates uu___331_16096 =
                             match uu___331_16096 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16111;
                                  FStar_Syntax_Syntax.p = uu____16112;_},FStar_Pervasives_Native.None
                                ,uu____16113) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16126;
                                  FStar_Syntax_Syntax.p = uu____16127;_},FStar_Pervasives_Native.None
                                ,uu____16128) -> true
                             | uu____16153 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16253 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16253 with
                                       | (uu____16254,uu____16255,t') ->
                                           let uu____16273 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____16273 with
                                            | (FullMatch ,uu____16284) ->
                                                true
                                            | (HeadMatch
                                               uu____16297,uu____16298) ->
                                                true
                                            | uu____16311 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16344 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16344
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16349 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16349 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16437,uu____16438) ->
                                       branches1
                                   | uu____16583 -> branches  in
                                 let uu____16638 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____16647 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____16647 with
                                        | (p,uu____16651,uu____16652) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____16638))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____16708 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____16708 with
                                | (p,uu____16716,e) ->
                                    ((let uu____16735 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____16735
                                      then
                                        let uu____16736 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____16737 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____16736 uu____16737
                                      else ());
                                     (let uu____16739 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____16739)))))
                 | uu____16752 ->
                     ((let uu____16774 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____16774
                       then
                         let uu____16775 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____16776 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____16775 uu____16776
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____16817 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____16817
            then
              let uu____16818 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16819 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____16820 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16821 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____16818 uu____16819 uu____16820 uu____16821
            else ());
           (let uu____16823 = head_matches_delta env1 t1 t2  in
            match uu____16823 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____16854,uu____16855) ->
                     let rec may_relate head3 =
                       let uu____16882 =
                         let uu____16883 = FStar_Syntax_Subst.compress head3
                            in
                         uu____16883.FStar_Syntax_Syntax.n  in
                       match uu____16882 with
                       | FStar_Syntax_Syntax.Tm_name uu____16886 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____16887 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____16910;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____16911;
                             FStar_Syntax_Syntax.fv_qual = uu____16912;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____16915;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____16916;
                             FStar_Syntax_Syntax.fv_qual = uu____16917;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____16921,uu____16922) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____16964) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____16970) ->
                           may_relate t
                       | uu____16975 -> false  in
                     let uu____16976 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____16976 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____16991 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____16991
                          then
                            let uu____16992 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____16992 with
                             | (guard,wl2) ->
                                 let uu____16999 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____16999)
                          else
                            (let uu____17001 =
                               let uu____17002 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____17003 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               FStar_Util.format2 "head mismatch (%s vs %s)"
                                 uu____17002 uu____17003
                                in
                             giveup env1 uu____17001 orig))
                 | (HeadMatch (true ),uu____17004) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____17017 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____17017 with
                        | (guard,wl2) ->
                            let uu____17024 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____17024)
                     else
                       (let uu____17026 =
                          let uu____17027 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____17028 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____17027 uu____17028
                           in
                        giveup env1 uu____17026 orig)
                 | (uu____17029,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___373_17043 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___373_17043.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___373_17043.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___373_17043.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___373_17043.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___373_17043.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___373_17043.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___373_17043.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___373_17043.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____17067 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____17067
          then
            let uu____17068 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____17068
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____17073 =
                let uu____17076 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____17076  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____17073 t1);
             (let uu____17088 =
                let uu____17091 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____17091  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____17088 t2);
             (let uu____17103 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____17103
              then
                let uu____17104 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____17105 =
                  let uu____17106 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____17107 =
                    let uu____17108 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____17108  in
                  Prims.strcat uu____17106 uu____17107  in
                let uu____17109 =
                  let uu____17110 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____17111 =
                    let uu____17112 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____17112  in
                  Prims.strcat uu____17110 uu____17111  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____17104
                  uu____17105 uu____17109
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____17115,uu____17116) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____17139,FStar_Syntax_Syntax.Tm_delayed uu____17140) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____17163,uu____17164) ->
                  let uu____17191 =
                    let uu___374_17192 = problem  in
                    let uu____17193 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___374_17192.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____17193;
                      FStar_TypeChecker_Common.relation =
                        (uu___374_17192.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___374_17192.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___374_17192.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___374_17192.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___374_17192.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___374_17192.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___374_17192.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___374_17192.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17191 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____17194,uu____17195) ->
                  let uu____17202 =
                    let uu___375_17203 = problem  in
                    let uu____17204 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___375_17203.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____17204;
                      FStar_TypeChecker_Common.relation =
                        (uu___375_17203.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___375_17203.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___375_17203.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___375_17203.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___375_17203.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___375_17203.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___375_17203.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___375_17203.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17202 wl
              | (uu____17205,FStar_Syntax_Syntax.Tm_ascribed uu____17206) ->
                  let uu____17233 =
                    let uu___376_17234 = problem  in
                    let uu____17235 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___376_17234.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___376_17234.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___376_17234.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____17235;
                      FStar_TypeChecker_Common.element =
                        (uu___376_17234.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___376_17234.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___376_17234.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___376_17234.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___376_17234.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___376_17234.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17233 wl
              | (uu____17236,FStar_Syntax_Syntax.Tm_meta uu____17237) ->
                  let uu____17244 =
                    let uu___377_17245 = problem  in
                    let uu____17246 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___377_17245.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___377_17245.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___377_17245.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____17246;
                      FStar_TypeChecker_Common.element =
                        (uu___377_17245.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___377_17245.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___377_17245.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___377_17245.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___377_17245.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___377_17245.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17244 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____17248),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____17250)) ->
                  let uu____17259 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____17259
              | (FStar_Syntax_Syntax.Tm_bvar uu____17260,uu____17261) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____17262,FStar_Syntax_Syntax.Tm_bvar uu____17263) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___332_17322 =
                    match uu___332_17322 with
                    | [] -> c
                    | bs ->
                        let uu____17344 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____17344
                     in
                  let uu____17353 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____17353 with
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
                                    let uu____17476 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____17476
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
                  let mk_t t l uu___333_17551 =
                    match uu___333_17551 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____17585 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____17585 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____17704 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____17705 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____17704
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____17705 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____17706,uu____17707) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____17734 -> true
                    | uu____17751 -> false  in
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
                      (let uu____17804 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___378_17812 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___378_17812.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___378_17812.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___378_17812.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___378_17812.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___378_17812.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___378_17812.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___378_17812.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___378_17812.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___378_17812.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___378_17812.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___378_17812.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___378_17812.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___378_17812.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___378_17812.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___378_17812.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___378_17812.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___378_17812.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___378_17812.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___378_17812.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___378_17812.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___378_17812.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___378_17812.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___378_17812.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___378_17812.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___378_17812.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___378_17812.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___378_17812.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___378_17812.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___378_17812.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___378_17812.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___378_17812.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___378_17812.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___378_17812.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___378_17812.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___378_17812.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___378_17812.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___378_17812.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___378_17812.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____17804 with
                       | (uu____17815,ty,uu____17817) ->
                           let uu____17818 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____17818)
                     in
                  let uu____17819 =
                    let uu____17836 = maybe_eta t1  in
                    let uu____17843 = maybe_eta t2  in
                    (uu____17836, uu____17843)  in
                  (match uu____17819 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___379_17885 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___379_17885.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___379_17885.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___379_17885.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___379_17885.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___379_17885.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___379_17885.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___379_17885.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___379_17885.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____17906 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____17906
                       then
                         let uu____17907 = destruct_flex_t not_abs wl  in
                         (match uu____17907 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___380_17922 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___380_17922.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___380_17922.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___380_17922.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___380_17922.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___380_17922.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___380_17922.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___380_17922.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___380_17922.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____17944 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____17944
                       then
                         let uu____17945 = destruct_flex_t not_abs wl  in
                         (match uu____17945 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___380_17960 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___380_17960.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___380_17960.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___380_17960.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___380_17960.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___380_17960.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___380_17960.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___380_17960.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___380_17960.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____17962 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____17979,FStar_Syntax_Syntax.Tm_abs uu____17980) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18007 -> true
                    | uu____18024 -> false  in
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
                      (let uu____18077 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___378_18085 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___378_18085.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___378_18085.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___378_18085.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___378_18085.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___378_18085.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___378_18085.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___378_18085.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___378_18085.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___378_18085.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___378_18085.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___378_18085.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___378_18085.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___378_18085.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___378_18085.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___378_18085.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___378_18085.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___378_18085.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___378_18085.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___378_18085.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___378_18085.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___378_18085.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___378_18085.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___378_18085.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___378_18085.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___378_18085.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___378_18085.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___378_18085.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___378_18085.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___378_18085.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___378_18085.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___378_18085.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___378_18085.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___378_18085.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___378_18085.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___378_18085.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___378_18085.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___378_18085.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___378_18085.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____18077 with
                       | (uu____18088,ty,uu____18090) ->
                           let uu____18091 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____18091)
                     in
                  let uu____18092 =
                    let uu____18109 = maybe_eta t1  in
                    let uu____18116 = maybe_eta t2  in
                    (uu____18109, uu____18116)  in
                  (match uu____18092 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___379_18158 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___379_18158.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___379_18158.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___379_18158.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___379_18158.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___379_18158.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___379_18158.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___379_18158.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___379_18158.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____18179 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18179
                       then
                         let uu____18180 = destruct_flex_t not_abs wl  in
                         (match uu____18180 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___380_18195 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___380_18195.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___380_18195.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___380_18195.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___380_18195.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___380_18195.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___380_18195.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___380_18195.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___380_18195.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____18217 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18217
                       then
                         let uu____18218 = destruct_flex_t not_abs wl  in
                         (match uu____18218 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___380_18233 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___380_18233.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___380_18233.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___380_18233.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___380_18233.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___380_18233.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___380_18233.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___380_18233.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___380_18233.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____18235 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____18264 =
                    let uu____18269 =
                      head_matches_delta env x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____18269 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___381_18297 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___381_18297.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___381_18297.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___382_18299 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___382_18299.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___382_18299.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____18300,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___381_18314 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___381_18314.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___381_18314.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___382_18316 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___382_18316.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___382_18316.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____18317 -> (x1, x2)  in
                  (match uu____18264 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____18336 = as_refinement false env t11  in
                       (match uu____18336 with
                        | (x12,phi11) ->
                            let uu____18343 = as_refinement false env t21  in
                            (match uu____18343 with
                             | (x22,phi21) ->
                                 ((let uu____18351 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____18351
                                   then
                                     ((let uu____18353 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____18354 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____18355 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____18353
                                         uu____18354 uu____18355);
                                      (let uu____18356 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____18357 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____18358 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____18356
                                         uu____18357 uu____18358))
                                   else ());
                                  (let uu____18360 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____18360 with
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
                                         let uu____18426 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____18426
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____18438 =
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
                                         (let uu____18449 =
                                            let uu____18452 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____18452
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____18449
                                            (p_guard base_prob));
                                         (let uu____18464 =
                                            let uu____18467 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____18467
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____18464
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____18479 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____18479)
                                          in
                                       let has_uvars =
                                         (let uu____18483 =
                                            let uu____18484 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____18484
                                             in
                                          Prims.op_Negation uu____18483) ||
                                           (let uu____18488 =
                                              let uu____18489 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____18489
                                               in
                                            Prims.op_Negation uu____18488)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____18492 =
                                           let uu____18497 =
                                             let uu____18504 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____18504]  in
                                           mk_t_problem wl1 uu____18497 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____18492 with
                                          | (ref_prob,wl2) ->
                                              let uu____18519 =
                                                solve env1
                                                  (let uu___383_18521 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___383_18521.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___383_18521.smt_ok);
                                                     tcenv =
                                                       (uu___383_18521.tcenv);
                                                     wl_implicits =
                                                       (uu___383_18521.wl_implicits)
                                                   })
                                                 in
                                              (match uu____18519 with
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
                                               | Success uu____18531 ->
                                                   let guard =
                                                     let uu____18539 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____18539
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___384_18548 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___384_18548.attempting);
                                                       wl_deferred =
                                                         (uu___384_18548.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___384_18548.defer_ok);
                                                       smt_ok =
                                                         (uu___384_18548.smt_ok);
                                                       tcenv =
                                                         (uu___384_18548.tcenv);
                                                       wl_implicits =
                                                         (uu___384_18548.wl_implicits)
                                                     }  in
                                                   let uu____18549 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____18549))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____18551,FStar_Syntax_Syntax.Tm_uvar uu____18552) ->
                  let uu____18577 = destruct_flex_t t1 wl  in
                  (match uu____18577 with
                   | (f1,wl1) ->
                       let uu____18584 = destruct_flex_t t2 wl1  in
                       (match uu____18584 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18591;
                    FStar_Syntax_Syntax.pos = uu____18592;
                    FStar_Syntax_Syntax.vars = uu____18593;_},uu____18594),FStar_Syntax_Syntax.Tm_uvar
                 uu____18595) ->
                  let uu____18640 = destruct_flex_t t1 wl  in
                  (match uu____18640 with
                   | (f1,wl1) ->
                       let uu____18647 = destruct_flex_t t2 wl1  in
                       (match uu____18647 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____18654,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18655;
                    FStar_Syntax_Syntax.pos = uu____18656;
                    FStar_Syntax_Syntax.vars = uu____18657;_},uu____18658))
                  ->
                  let uu____18703 = destruct_flex_t t1 wl  in
                  (match uu____18703 with
                   | (f1,wl1) ->
                       let uu____18710 = destruct_flex_t t2 wl1  in
                       (match uu____18710 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18717;
                    FStar_Syntax_Syntax.pos = uu____18718;
                    FStar_Syntax_Syntax.vars = uu____18719;_},uu____18720),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18721;
                    FStar_Syntax_Syntax.pos = uu____18722;
                    FStar_Syntax_Syntax.vars = uu____18723;_},uu____18724))
                  ->
                  let uu____18789 = destruct_flex_t t1 wl  in
                  (match uu____18789 with
                   | (f1,wl1) ->
                       let uu____18796 = destruct_flex_t t2 wl1  in
                       (match uu____18796 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____18803,uu____18804) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____18817 = destruct_flex_t t1 wl  in
                  (match uu____18817 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18824;
                    FStar_Syntax_Syntax.pos = uu____18825;
                    FStar_Syntax_Syntax.vars = uu____18826;_},uu____18827),uu____18828)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____18861 = destruct_flex_t t1 wl  in
                  (match uu____18861 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____18868,FStar_Syntax_Syntax.Tm_uvar uu____18869) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____18882,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18883;
                    FStar_Syntax_Syntax.pos = uu____18884;
                    FStar_Syntax_Syntax.vars = uu____18885;_},uu____18886))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____18919,FStar_Syntax_Syntax.Tm_arrow uu____18920) ->
                  solve_t' env
                    (let uu___385_18946 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___385_18946.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___385_18946.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___385_18946.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___385_18946.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___385_18946.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___385_18946.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___385_18946.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___385_18946.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___385_18946.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18947;
                    FStar_Syntax_Syntax.pos = uu____18948;
                    FStar_Syntax_Syntax.vars = uu____18949;_},uu____18950),FStar_Syntax_Syntax.Tm_arrow
                 uu____18951) ->
                  solve_t' env
                    (let uu___385_18997 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___385_18997.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___385_18997.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___385_18997.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___385_18997.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___385_18997.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___385_18997.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___385_18997.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___385_18997.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___385_18997.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____18998,FStar_Syntax_Syntax.Tm_uvar uu____18999) ->
                  let uu____19012 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19012
              | (uu____19013,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19014;
                    FStar_Syntax_Syntax.pos = uu____19015;
                    FStar_Syntax_Syntax.vars = uu____19016;_},uu____19017))
                  ->
                  let uu____19050 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19050
              | (FStar_Syntax_Syntax.Tm_uvar uu____19051,uu____19052) ->
                  let uu____19065 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19065
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19066;
                    FStar_Syntax_Syntax.pos = uu____19067;
                    FStar_Syntax_Syntax.vars = uu____19068;_},uu____19069),uu____19070)
                  ->
                  let uu____19103 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19103
              | (FStar_Syntax_Syntax.Tm_refine uu____19104,uu____19105) ->
                  let t21 =
                    let uu____19113 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____19113  in
                  solve_t env
                    (let uu___386_19139 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___386_19139.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___386_19139.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___386_19139.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___386_19139.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___386_19139.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___386_19139.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___386_19139.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___386_19139.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___386_19139.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____19140,FStar_Syntax_Syntax.Tm_refine uu____19141) ->
                  let t11 =
                    let uu____19149 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____19149  in
                  solve_t env
                    (let uu___387_19175 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___387_19175.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___387_19175.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___387_19175.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___387_19175.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___387_19175.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___387_19175.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___387_19175.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___387_19175.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___387_19175.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____19257 =
                    let uu____19258 = guard_of_prob env wl problem t1 t2  in
                    match uu____19258 with
                    | (guard,wl1) ->
                        let uu____19265 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____19265
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____19476 = br1  in
                        (match uu____19476 with
                         | (p1,w1,uu____19501) ->
                             let uu____19518 = br2  in
                             (match uu____19518 with
                              | (p2,w2,uu____19537) ->
                                  let uu____19542 =
                                    let uu____19543 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____19543  in
                                  if uu____19542
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____19559 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____19559 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____19592 = br2  in
                                         (match uu____19592 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____19627 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____19627
                                                 in
                                              let uu____19638 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____19661,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____19678) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____19721 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____19721 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____19638
                                                (fun uu____19763  ->
                                                   match uu____19763 with
                                                   | (wprobs,wl2) ->
                                                       let uu____19784 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____19784
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____19799 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____19799
                                                              (fun
                                                                 uu____19823 
                                                                 ->
                                                                 match uu____19823
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____19908 -> FStar_Pervasives_Native.None  in
                  let uu____19945 = solve_branches wl brs1 brs2  in
                  (match uu____19945 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____19973 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____19973 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____19990 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____19990  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____19999 =
                              let uu____20000 =
                                attempt sub_probs1
                                  (let uu___388_20002 = wl3  in
                                   {
                                     attempting = (uu___388_20002.attempting);
                                     wl_deferred =
                                       (uu___388_20002.wl_deferred);
                                     ctr = (uu___388_20002.ctr);
                                     defer_ok = (uu___388_20002.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___388_20002.tcenv);
                                     wl_implicits =
                                       (uu___388_20002.wl_implicits)
                                   })
                                 in
                              solve env uu____20000  in
                            (match uu____19999 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____20006 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____20012,uu____20013) ->
                  let head1 =
                    let uu____20037 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20037
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20077 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20077
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20117 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20117
                    then
                      let uu____20118 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20119 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20120 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20118 uu____20119 uu____20120
                    else ());
                   (let no_free_uvars t =
                      (let uu____20130 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____20130) &&
                        (let uu____20134 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____20134)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____20150 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____20150 = FStar_Syntax_Util.Equal  in
                    let uu____20151 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____20151
                    then
                      let uu____20152 =
                        let uu____20159 = equal t1 t2  in
                        if uu____20159
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____20169 = mk_eq2 wl orig t1 t2  in
                           match uu____20169 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____20152 with
                      | (guard,wl1) ->
                          let uu____20190 = solve_prob orig guard [] wl1  in
                          solve env uu____20190
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____20192,uu____20193) ->
                  let head1 =
                    let uu____20201 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20201
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20241 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20241
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20281 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20281
                    then
                      let uu____20282 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20283 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20284 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20282 uu____20283 uu____20284
                    else ());
                   (let no_free_uvars t =
                      (let uu____20294 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____20294) &&
                        (let uu____20298 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____20298)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____20314 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____20314 = FStar_Syntax_Util.Equal  in
                    let uu____20315 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____20315
                    then
                      let uu____20316 =
                        let uu____20323 = equal t1 t2  in
                        if uu____20323
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____20333 = mk_eq2 wl orig t1 t2  in
                           match uu____20333 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____20316 with
                      | (guard,wl1) ->
                          let uu____20354 = solve_prob orig guard [] wl1  in
                          solve env uu____20354
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____20356,uu____20357) ->
                  let head1 =
                    let uu____20359 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20359
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20399 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20399
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20439 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20439
                    then
                      let uu____20440 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20441 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20442 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20440 uu____20441 uu____20442
                    else ());
                   (let no_free_uvars t =
                      (let uu____20452 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____20452) &&
                        (let uu____20456 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____20456)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____20472 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____20472 = FStar_Syntax_Util.Equal  in
                    let uu____20473 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____20473
                    then
                      let uu____20474 =
                        let uu____20481 = equal t1 t2  in
                        if uu____20481
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____20491 = mk_eq2 wl orig t1 t2  in
                           match uu____20491 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____20474 with
                      | (guard,wl1) ->
                          let uu____20512 = solve_prob orig guard [] wl1  in
                          solve env uu____20512
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____20514,uu____20515) ->
                  let head1 =
                    let uu____20517 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20517
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20557 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20557
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20597 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20597
                    then
                      let uu____20598 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20599 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20600 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20598 uu____20599 uu____20600
                    else ());
                   (let no_free_uvars t =
                      (let uu____20610 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____20610) &&
                        (let uu____20614 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____20614)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____20630 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____20630 = FStar_Syntax_Util.Equal  in
                    let uu____20631 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____20631
                    then
                      let uu____20632 =
                        let uu____20639 = equal t1 t2  in
                        if uu____20639
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____20649 = mk_eq2 wl orig t1 t2  in
                           match uu____20649 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____20632 with
                      | (guard,wl1) ->
                          let uu____20670 = solve_prob orig guard [] wl1  in
                          solve env uu____20670
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____20672,uu____20673) ->
                  let head1 =
                    let uu____20675 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20675
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20715 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20715
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20755 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20755
                    then
                      let uu____20756 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20757 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20758 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20756 uu____20757 uu____20758
                    else ());
                   (let no_free_uvars t =
                      (let uu____20768 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____20768) &&
                        (let uu____20772 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____20772)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____20788 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____20788 = FStar_Syntax_Util.Equal  in
                    let uu____20789 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____20789
                    then
                      let uu____20790 =
                        let uu____20797 = equal t1 t2  in
                        if uu____20797
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____20807 = mk_eq2 wl orig t1 t2  in
                           match uu____20807 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____20790 with
                      | (guard,wl1) ->
                          let uu____20828 = solve_prob orig guard [] wl1  in
                          solve env uu____20828
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____20830,uu____20831) ->
                  let head1 =
                    let uu____20847 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20847
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20887 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20887
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20927 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20927
                    then
                      let uu____20928 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20929 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20930 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20928 uu____20929 uu____20930
                    else ());
                   (let no_free_uvars t =
                      (let uu____20940 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____20940) &&
                        (let uu____20944 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____20944)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____20960 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____20960 = FStar_Syntax_Util.Equal  in
                    let uu____20961 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____20961
                    then
                      let uu____20962 =
                        let uu____20969 = equal t1 t2  in
                        if uu____20969
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____20979 = mk_eq2 wl orig t1 t2  in
                           match uu____20979 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____20962 with
                      | (guard,wl1) ->
                          let uu____21000 = solve_prob orig guard [] wl1  in
                          solve env uu____21000
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21002,FStar_Syntax_Syntax.Tm_match uu____21003) ->
                  let head1 =
                    let uu____21027 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21027
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21067 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21067
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21107 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21107
                    then
                      let uu____21108 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21109 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21110 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21108 uu____21109 uu____21110
                    else ());
                   (let no_free_uvars t =
                      (let uu____21120 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21120) &&
                        (let uu____21124 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21124)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____21140 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21140 = FStar_Syntax_Util.Equal  in
                    let uu____21141 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21141
                    then
                      let uu____21142 =
                        let uu____21149 = equal t1 t2  in
                        if uu____21149
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21159 = mk_eq2 wl orig t1 t2  in
                           match uu____21159 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21142 with
                      | (guard,wl1) ->
                          let uu____21180 = solve_prob orig guard [] wl1  in
                          solve env uu____21180
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21182,FStar_Syntax_Syntax.Tm_uinst uu____21183) ->
                  let head1 =
                    let uu____21191 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21191
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21225 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21225
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21259 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21259
                    then
                      let uu____21260 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21261 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21262 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21260 uu____21261 uu____21262
                    else ());
                   (let no_free_uvars t =
                      (let uu____21272 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21272) &&
                        (let uu____21276 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21276)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____21292 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21292 = FStar_Syntax_Util.Equal  in
                    let uu____21293 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21293
                    then
                      let uu____21294 =
                        let uu____21301 = equal t1 t2  in
                        if uu____21301
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21311 = mk_eq2 wl orig t1 t2  in
                           match uu____21311 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21294 with
                      | (guard,wl1) ->
                          let uu____21332 = solve_prob orig guard [] wl1  in
                          solve env uu____21332
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21334,FStar_Syntax_Syntax.Tm_name uu____21335) ->
                  let head1 =
                    let uu____21337 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21337
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21371 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21371
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21405 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21405
                    then
                      let uu____21406 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21407 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21408 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21406 uu____21407 uu____21408
                    else ());
                   (let no_free_uvars t =
                      (let uu____21418 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21418) &&
                        (let uu____21422 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21422)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____21438 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21438 = FStar_Syntax_Util.Equal  in
                    let uu____21439 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21439
                    then
                      let uu____21440 =
                        let uu____21447 = equal t1 t2  in
                        if uu____21447
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21457 = mk_eq2 wl orig t1 t2  in
                           match uu____21457 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21440 with
                      | (guard,wl1) ->
                          let uu____21478 = solve_prob orig guard [] wl1  in
                          solve env uu____21478
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21480,FStar_Syntax_Syntax.Tm_constant uu____21481) ->
                  let head1 =
                    let uu____21483 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21483
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21517 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21517
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21551 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21551
                    then
                      let uu____21552 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21553 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21554 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21552 uu____21553 uu____21554
                    else ());
                   (let no_free_uvars t =
                      (let uu____21564 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21564) &&
                        (let uu____21568 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21568)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____21584 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21584 = FStar_Syntax_Util.Equal  in
                    let uu____21585 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21585
                    then
                      let uu____21586 =
                        let uu____21593 = equal t1 t2  in
                        if uu____21593
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21603 = mk_eq2 wl orig t1 t2  in
                           match uu____21603 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21586 with
                      | (guard,wl1) ->
                          let uu____21624 = solve_prob orig guard [] wl1  in
                          solve env uu____21624
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21626,FStar_Syntax_Syntax.Tm_fvar uu____21627) ->
                  let head1 =
                    let uu____21629 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21629
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21669 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21669
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21709 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21709
                    then
                      let uu____21710 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21711 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21712 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21710 uu____21711 uu____21712
                    else ());
                   (let no_free_uvars t =
                      (let uu____21722 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21722) &&
                        (let uu____21726 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21726)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____21742 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21742 = FStar_Syntax_Util.Equal  in
                    let uu____21743 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21743
                    then
                      let uu____21744 =
                        let uu____21751 = equal t1 t2  in
                        if uu____21751
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21761 = mk_eq2 wl orig t1 t2  in
                           match uu____21761 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21744 with
                      | (guard,wl1) ->
                          let uu____21782 = solve_prob orig guard [] wl1  in
                          solve env uu____21782
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21784,FStar_Syntax_Syntax.Tm_app uu____21785) ->
                  let head1 =
                    let uu____21801 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21801
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21835 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21835
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21869 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21869
                    then
                      let uu____21870 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21871 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21872 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21870 uu____21871 uu____21872
                    else ());
                   (let no_free_uvars t =
                      (let uu____21882 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21882) &&
                        (let uu____21886 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21886)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Iota] env t21
                         in
                      let uu____21902 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21902 = FStar_Syntax_Util.Equal  in
                    let uu____21903 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21903
                    then
                      let uu____21904 =
                        let uu____21911 = equal t1 t2  in
                        if uu____21911
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21921 = mk_eq2 wl orig t1 t2  in
                           match uu____21921 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21904 with
                      | (guard,wl1) ->
                          let uu____21942 = solve_prob orig guard [] wl1  in
                          solve env uu____21942
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____21944,FStar_Syntax_Syntax.Tm_let uu____21945) ->
                  let uu____21970 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____21970
                  then
                    let uu____21971 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____21971
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____21973,uu____21974) ->
                  let uu____21987 =
                    let uu____21992 =
                      let uu____21993 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____21994 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____21995 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____21996 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____21993 uu____21994 uu____21995 uu____21996
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____21992)
                     in
                  FStar_Errors.raise_error uu____21987
                    t1.FStar_Syntax_Syntax.pos
              | (uu____21997,FStar_Syntax_Syntax.Tm_let uu____21998) ->
                  let uu____22011 =
                    let uu____22016 =
                      let uu____22017 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____22018 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____22019 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____22020 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____22017 uu____22018 uu____22019 uu____22020
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____22016)
                     in
                  FStar_Errors.raise_error uu____22011
                    t1.FStar_Syntax_Syntax.pos
              | uu____22021 -> giveup env "head tag mismatch" orig))))

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
          (let uu____22080 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____22080
           then
             let uu____22081 =
               let uu____22082 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____22082  in
             let uu____22083 =
               let uu____22084 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____22084  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____22081 uu____22083
           else ());
          (let uu____22086 =
             let uu____22087 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____22087  in
           if uu____22086
           then
             let uu____22088 =
               let uu____22089 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____22090 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____22089 uu____22090
                in
             giveup env uu____22088 orig
           else
             (let uu____22092 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____22092 with
              | (ret_sub_prob,wl1) ->
                  let uu____22099 =
                    FStar_List.fold_right2
                      (fun uu____22132  ->
                         fun uu____22133  ->
                           fun uu____22134  ->
                             match (uu____22132, uu____22133, uu____22134)
                             with
                             | ((a1,uu____22170),(a2,uu____22172),(arg_sub_probs,wl2))
                                 ->
                                 let uu____22193 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____22193 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____22099 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____22222 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____22222  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____22230 = attempt sub_probs wl3  in
                       solve env uu____22230)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____22253 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22256)::[] -> wp1
              | uu____22273 ->
                  let uu____22282 =
                    let uu____22283 =
                      let uu____22284 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____22284  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____22283
                     in
                  failwith uu____22282
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____22290 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____22290]
              | x -> x  in
            let uu____22292 =
              let uu____22301 =
                let uu____22308 =
                  let uu____22309 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____22309 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____22308  in
              [uu____22301]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____22292;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____22322 = lift_c1 ()  in solve_eq uu____22322 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___334_22328  ->
                       match uu___334_22328 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____22329 -> false))
                in
             let uu____22330 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____22356)::uu____22357,(wp2,uu____22359)::uu____22360)
                   -> (wp1, wp2)
               | uu____22413 ->
                   let uu____22434 =
                     let uu____22439 =
                       let uu____22440 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____22441 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____22440 uu____22441
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____22439)
                      in
                   FStar_Errors.raise_error uu____22434
                     env.FStar_TypeChecker_Env.range
                in
             match uu____22330 with
             | (wpc1,wpc2) ->
                 let uu____22448 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____22448
                 then
                   let uu____22451 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____22451 wl
                 else
                   (let uu____22453 =
                      let uu____22460 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____22460  in
                    match uu____22453 with
                    | (c2_decl,qualifiers) ->
                        let uu____22481 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____22481
                        then
                          let c1_repr =
                            let uu____22485 =
                              let uu____22486 =
                                let uu____22487 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____22487  in
                              let uu____22488 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22486 uu____22488
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____22485
                             in
                          let c2_repr =
                            let uu____22490 =
                              let uu____22491 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____22492 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22491 uu____22492
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____22490
                             in
                          let uu____22493 =
                            let uu____22498 =
                              let uu____22499 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____22500 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____22499 uu____22500
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____22498
                             in
                          (match uu____22493 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____22504 = attempt [prob] wl2  in
                               solve env uu____22504)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____22515 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22515
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____22518 =
                                     let uu____22525 =
                                       let uu____22526 =
                                         let uu____22541 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____22544 =
                                           let uu____22553 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____22560 =
                                             let uu____22569 =
                                               let uu____22576 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____22576
                                                in
                                             [uu____22569]  in
                                           uu____22553 :: uu____22560  in
                                         (uu____22541, uu____22544)  in
                                       FStar_Syntax_Syntax.Tm_app uu____22526
                                        in
                                     FStar_Syntax_Syntax.mk uu____22525  in
                                   uu____22518 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____22617 =
                                    let uu____22624 =
                                      let uu____22625 =
                                        let uu____22640 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____22643 =
                                          let uu____22652 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____22659 =
                                            let uu____22668 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____22675 =
                                              let uu____22684 =
                                                let uu____22691 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____22691
                                                 in
                                              [uu____22684]  in
                                            uu____22668 :: uu____22675  in
                                          uu____22652 :: uu____22659  in
                                        (uu____22640, uu____22643)  in
                                      FStar_Syntax_Syntax.Tm_app uu____22625
                                       in
                                    FStar_Syntax_Syntax.mk uu____22624  in
                                  uu____22617 FStar_Pervasives_Native.None r)
                              in
                           (let uu____22736 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____22736
                            then
                              let uu____22737 =
                                let uu____22738 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Iota;
                                    FStar_TypeChecker_Normalize.Eager_unfolding;
                                    FStar_TypeChecker_Normalize.Primops;
                                    FStar_TypeChecker_Normalize.Simplify] env
                                    g
                                   in
                                FStar_Syntax_Print.term_to_string uu____22738
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____22737
                            else ());
                           (let uu____22740 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____22740 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____22748 =
                                    let uu____22751 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____22751
                                     in
                                  solve_prob orig uu____22748 [] wl1  in
                                let uu____22754 = attempt [base_prob] wl2  in
                                solve env uu____22754))))
           in
        let uu____22755 = FStar_Util.physical_equality c1 c2  in
        if uu____22755
        then
          let uu____22756 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____22756
        else
          ((let uu____22759 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____22759
            then
              let uu____22760 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____22761 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____22760
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____22761
            else ());
           (let uu____22763 =
              let uu____22772 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____22775 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____22772, uu____22775)  in
            match uu____22763 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____22793),FStar_Syntax_Syntax.Total
                    (t2,uu____22795)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____22812 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22812 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____22813,FStar_Syntax_Syntax.Total uu____22814) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____22832),FStar_Syntax_Syntax.Total
                    (t2,uu____22834)) ->
                     let uu____22851 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22851 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____22853),FStar_Syntax_Syntax.GTotal
                    (t2,uu____22855)) ->
                     let uu____22872 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22872 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____22874),FStar_Syntax_Syntax.GTotal
                    (t2,uu____22876)) ->
                     let uu____22893 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22893 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____22894,FStar_Syntax_Syntax.Comp uu____22895) ->
                     let uu____22904 =
                       let uu___389_22907 = problem  in
                       let uu____22910 =
                         let uu____22911 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22911
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___389_22907.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____22910;
                         FStar_TypeChecker_Common.relation =
                           (uu___389_22907.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___389_22907.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___389_22907.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___389_22907.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___389_22907.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___389_22907.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___389_22907.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___389_22907.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22904 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____22912,FStar_Syntax_Syntax.Comp uu____22913) ->
                     let uu____22922 =
                       let uu___389_22925 = problem  in
                       let uu____22928 =
                         let uu____22929 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22929
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___389_22925.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____22928;
                         FStar_TypeChecker_Common.relation =
                           (uu___389_22925.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___389_22925.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___389_22925.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___389_22925.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___389_22925.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___389_22925.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___389_22925.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___389_22925.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22922 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22930,FStar_Syntax_Syntax.GTotal uu____22931) ->
                     let uu____22940 =
                       let uu___390_22943 = problem  in
                       let uu____22946 =
                         let uu____22947 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22947
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___390_22943.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___390_22943.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___390_22943.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____22946;
                         FStar_TypeChecker_Common.element =
                           (uu___390_22943.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___390_22943.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___390_22943.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___390_22943.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___390_22943.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___390_22943.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22940 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22948,FStar_Syntax_Syntax.Total uu____22949) ->
                     let uu____22958 =
                       let uu___390_22961 = problem  in
                       let uu____22964 =
                         let uu____22965 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22965
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___390_22961.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___390_22961.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___390_22961.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____22964;
                         FStar_TypeChecker_Common.element =
                           (uu___390_22961.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___390_22961.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___390_22961.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___390_22961.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___390_22961.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___390_22961.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22958 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22966,FStar_Syntax_Syntax.Comp uu____22967) ->
                     let uu____22968 =
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
                     if uu____22968
                     then
                       let uu____22969 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____22969 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____22973 =
                            let uu____22978 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____22978
                            then (c1_comp, c2_comp)
                            else
                              (let uu____22984 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____22985 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____22984, uu____22985))
                             in
                          match uu____22973 with
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
                           (let uu____22992 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____22992
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____22994 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____22994 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____22997 =
                                  let uu____22998 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____22999 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____22998 uu____22999
                                   in
                                giveup env uu____22997 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____23006 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____23006 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____23047 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____23047 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____23065 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____23093  ->
                match uu____23093 with
                | (u1,u2) ->
                    let uu____23100 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____23101 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____23100 uu____23101))
         in
      FStar_All.pipe_right uu____23065 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23128,[])) -> "{}"
      | uu____23153 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23176 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____23176
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____23179 =
              FStar_List.map
                (fun uu____23189  ->
                   match uu____23189 with
                   | (uu____23194,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____23179 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____23199 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23199 imps
  
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
                  let uu____23252 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____23252
                  then
                    let uu____23253 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____23254 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____23253
                      (rel_to_string rel) uu____23254
                  else "TOP"  in
                let uu____23256 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____23256 with
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
              let uu____23314 =
                let uu____23317 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____23317
                 in
              FStar_Syntax_Syntax.new_bv uu____23314 t1  in
            let uu____23320 =
              let uu____23325 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____23325
               in
            match uu____23320 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____23398 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____23398
              then
                let uu____23399 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____23399
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
          ((let uu____23421 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____23421
            then
              let uu____23422 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____23422
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____23426 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____23426
             then
               let uu____23427 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____23427
             else ());
            (let f2 =
               let uu____23430 =
                 let uu____23431 = FStar_Syntax_Util.unmeta f1  in
                 uu____23431.FStar_Syntax_Syntax.n  in
               match uu____23430 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____23435 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___391_23436 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___391_23436.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___391_23436.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___391_23436.FStar_TypeChecker_Env.implicits)
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
            let uu____23490 =
              let uu____23491 =
                let uu____23492 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____23492;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____23491  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____23490
  
let with_guard_no_simp :
  'Auu____23507 .
    'Auu____23507 ->
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
            let uu____23530 =
              let uu____23531 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____23531;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____23530
  
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
          (let uu____23561 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____23561
           then
             let uu____23562 = FStar_Syntax_Print.term_to_string t1  in
             let uu____23563 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____23562
               uu____23563
           else ());
          (let uu____23565 =
             let uu____23570 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____23570
              in
           match uu____23565 with
           | (prob,wl) ->
               let g =
                 let uu____23578 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____23588  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____23578  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23622 = try_teq true env t1 t2  in
        match uu____23622 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____23626 = FStar_TypeChecker_Env.get_range env  in
              let uu____23627 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____23626 uu____23627);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____23634 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____23634
              then
                let uu____23635 = FStar_Syntax_Print.term_to_string t1  in
                let uu____23636 = FStar_Syntax_Print.term_to_string t2  in
                let uu____23637 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____23635
                  uu____23636 uu____23637
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
          let uu____23659 = FStar_TypeChecker_Env.get_range env  in
          let uu____23660 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____23659 uu____23660
  
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
        (let uu____23685 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23685
         then
           let uu____23686 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____23687 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____23686 uu____23687
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____23690 =
           let uu____23697 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____23697 "sub_comp"
            in
         match uu____23690 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____23708 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____23718  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____23708)))
  
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
      fun uu____23763  ->
        match uu____23763 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____23806 =
                 let uu____23811 =
                   let uu____23812 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____23813 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____23812 uu____23813
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____23811)  in
               let uu____23814 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____23806 uu____23814)
               in
            let equiv1 v1 v' =
              let uu____23826 =
                let uu____23831 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____23832 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____23831, uu____23832)  in
              match uu____23826 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____23851 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____23881 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____23881 with
                      | FStar_Syntax_Syntax.U_unif uu____23888 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____23917  ->
                                    match uu____23917 with
                                    | (u,v') ->
                                        let uu____23926 = equiv1 v1 v'  in
                                        if uu____23926
                                        then
                                          let uu____23929 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____23929 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____23945 -> []))
               in
            let uu____23950 =
              let wl =
                let uu___392_23954 = empty_worklist env  in
                {
                  attempting = (uu___392_23954.attempting);
                  wl_deferred = (uu___392_23954.wl_deferred);
                  ctr = (uu___392_23954.ctr);
                  defer_ok = false;
                  smt_ok = (uu___392_23954.smt_ok);
                  tcenv = (uu___392_23954.tcenv);
                  wl_implicits = (uu___392_23954.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____23972  ->
                      match uu____23972 with
                      | (lb,v1) ->
                          let uu____23979 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____23979 with
                           | USolved wl1 -> ()
                           | uu____23981 -> fail1 lb v1)))
               in
            let rec check_ineq uu____23991 =
              match uu____23991 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24000) -> true
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
                      uu____24023,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24025,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24036) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24043,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24051 -> false)
               in
            let uu____24056 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24071  ->
                      match uu____24071 with
                      | (u,v1) ->
                          let uu____24078 = check_ineq (u, v1)  in
                          if uu____24078
                          then true
                          else
                            ((let uu____24081 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____24081
                              then
                                let uu____24082 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____24083 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____24082
                                  uu____24083
                              else ());
                             false)))
               in
            if uu____24056
            then ()
            else
              ((let uu____24087 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____24087
                then
                  ((let uu____24089 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____24089);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____24099 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____24099))
                else ());
               (let uu____24109 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____24109))
  
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
        let fail1 uu____24176 =
          match uu____24176 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___393_24197 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___393_24197.attempting);
            wl_deferred = (uu___393_24197.wl_deferred);
            ctr = (uu___393_24197.ctr);
            defer_ok;
            smt_ok = (uu___393_24197.smt_ok);
            tcenv = (uu___393_24197.tcenv);
            wl_implicits = (uu___393_24197.wl_implicits)
          }  in
        (let uu____24199 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24199
         then
           let uu____24200 = FStar_Util.string_of_bool defer_ok  in
           let uu____24201 = wl_to_string wl  in
           let uu____24202 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____24200 uu____24201 uu____24202
         else ());
        (let g1 =
           let uu____24205 = solve_and_commit env wl fail1  in
           match uu____24205 with
           | FStar_Pervasives_Native.Some
               (uu____24212::uu____24213,uu____24214) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___394_24239 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___394_24239.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___394_24239.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____24240 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___395_24248 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___395_24248.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___395_24248.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___395_24248.FStar_TypeChecker_Env.implicits)
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
    let uu____24296 = FStar_ST.op_Bang last_proof_ns  in
    match uu____24296 with
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
            let uu___396_24419 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___396_24419.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___396_24419.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___396_24419.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____24420 =
            let uu____24421 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____24421  in
          if uu____24420
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____24429 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____24430 =
                       let uu____24431 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24431
                        in
                     FStar_Errors.diag uu____24429 uu____24430)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____24435 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____24436 =
                        let uu____24437 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____24437
                         in
                      FStar_Errors.diag uu____24435 uu____24436)
                   else ();
                   (let uu____24440 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____24440
                      "discharge_guard'" env vc1);
                   (let uu____24441 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____24441 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____24448 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24449 =
                                let uu____24450 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____24450
                                 in
                              FStar_Errors.diag uu____24448 uu____24449)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____24455 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24456 =
                                let uu____24457 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____24457
                                 in
                              FStar_Errors.diag uu____24455 uu____24456)
                           else ();
                           (let vcs =
                              let uu____24468 = FStar_Options.use_tactics ()
                                 in
                              if uu____24468
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____24488  ->
                                     (let uu____24490 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____24490);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____24533  ->
                                              match uu____24533 with
                                              | (env1,goal,opts) ->
                                                  let uu____24549 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____24549, opts)))))
                              else
                                (let uu____24551 =
                                   let uu____24558 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____24558)  in
                                 [uu____24551])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____24591  ->
                                    match uu____24591 with
                                    | (env1,goal,opts) ->
                                        let uu____24601 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____24601 with
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
                                                (let uu____24609 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____24610 =
                                                   let uu____24611 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____24612 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____24611 uu____24612
                                                    in
                                                 FStar_Errors.diag
                                                   uu____24609 uu____24610)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____24615 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____24616 =
                                                   let uu____24617 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____24617
                                                    in
                                                 FStar_Errors.diag
                                                   uu____24615 uu____24616)
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
      let uu____24631 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____24631 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____24638 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____24638
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____24649 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____24649 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
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
            let uu____24682 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____24682 with
            | FStar_Pervasives_Native.Some uu____24685 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____24705 = acc  in
            match uu____24705 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____24717 = hd1  in
                     (match uu____24717 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____24723 = unresolved ctx_u  in
                             if uu____24723
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___397_24727 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___397_24727.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___397_24727.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___397_24727.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___397_24727.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___397_24727.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___397_24727.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___397_24727.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___397_24727.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___397_24727.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___397_24727.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___397_24727.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___397_24727.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___397_24727.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___397_24727.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___397_24727.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___397_24727.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___397_24727.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___397_24727.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___397_24727.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___397_24727.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___397_24727.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___397_24727.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___397_24727.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___397_24727.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___397_24727.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___397_24727.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___397_24727.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___397_24727.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___397_24727.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___397_24727.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___397_24727.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___397_24727.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___397_24727.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___397_24727.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___397_24727.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___397_24727.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___397_24727.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___397_24727.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___397_24727.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___397_24727.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___398_24730 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___398_24730.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___398_24730.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___398_24730.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___398_24730.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___398_24730.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___398_24730.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___398_24730.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___398_24730.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___398_24730.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___398_24730.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___398_24730.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___398_24730.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___398_24730.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___398_24730.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___398_24730.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___398_24730.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___398_24730.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___398_24730.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___398_24730.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___398_24730.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___398_24730.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___398_24730.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___398_24730.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___398_24730.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___398_24730.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___398_24730.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___398_24730.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___398_24730.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___398_24730.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___398_24730.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___398_24730.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___398_24730.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___398_24730.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___398_24730.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___398_24730.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___398_24730.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___398_24730.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___398_24730.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___398_24730.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___398_24730.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____24733 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24733
                                   then
                                     let uu____24734 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____24735 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____24736 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____24737 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____24734 uu____24735 uu____24736
                                       reason uu____24737
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____24748 =
                                             let uu____24757 =
                                               let uu____24764 =
                                                 let uu____24765 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____24766 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____24767 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____24765 uu____24766
                                                   uu____24767
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____24764, r)
                                                in
                                             [uu____24757]  in
                                           FStar_Errors.add_errors
                                             uu____24748);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___401_24781 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___401_24781.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___401_24781.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___401_24781.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____24784 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____24794  ->
                                               let uu____24795 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____24796 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____24797 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____24795 uu____24796
                                                 reason uu____24797)) env2 g2
                                         true
                                        in
                                     match uu____24784 with
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
          let uu___402_24799 = g  in
          let uu____24800 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___402_24799.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___402_24799.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___402_24799.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____24800
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
        let uu____24834 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____24834 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____24835 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____24835
      | imp::uu____24837 ->
          let uu____24840 =
            let uu____24845 =
              let uu____24846 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____24847 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____24846 uu____24847 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____24845)
             in
          FStar_Errors.raise_error uu____24840
            imp.FStar_TypeChecker_Env.imp_range
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___403_24858 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___403_24858.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___403_24858.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___403_24858.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____24873 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____24873 with
      | FStar_Pervasives_Native.Some uu____24879 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24895 = try_teq false env t1 t2  in
        match uu____24895 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
  
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
        (let uu____24929 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24929
         then
           let uu____24930 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____24931 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____24930
             uu____24931
         else ());
        (let uu____24933 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____24933 with
         | (prob,x,wl) ->
             let g =
               let uu____24952 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____24962  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____24952  in
             ((let uu____24982 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____24982
               then
                 let uu____24983 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____24984 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____24985 =
                   let uu____24986 = FStar_Util.must g  in
                   guard_to_string env uu____24986  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____24983 uu____24984 uu____24985
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
        let uu____25020 = check_subtyping env t1 t2  in
        match uu____25020 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25039 =
              let uu____25040 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____25040 g  in
            FStar_Pervasives_Native.Some uu____25039
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25058 = check_subtyping env t1 t2  in
        match uu____25058 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25077 =
              let uu____25078 =
                let uu____25079 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____25079]  in
              FStar_TypeChecker_Env.close_guard env uu____25078 g  in
            FStar_Pervasives_Native.Some uu____25077
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____25108 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25108
         then
           let uu____25109 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25110 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____25109
             uu____25110
         else ());
        (let uu____25112 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____25112 with
         | (prob,x,wl) ->
             let g =
               let uu____25125 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____25135  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25125  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____25156 =
                      let uu____25157 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____25157]  in
                    FStar_TypeChecker_Env.close_guard env uu____25156 g1  in
                  discharge_guard_nosmt env g2))
  