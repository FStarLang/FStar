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
                  let uu____355 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____355;
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
                   (let uu___338_390 = wl  in
                    {
                      attempting = (uu___338_390.attempting);
                      wl_deferred = (uu___338_390.wl_deferred);
                      ctr = (uu___338_390.ctr);
                      defer_ok = (uu___338_390.defer_ok);
                      smt_ok = (uu___338_390.smt_ok);
                      tcenv = (uu___338_390.tcenv);
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
            let uu___339_422 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___339_422.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___339_422.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___339_422.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___339_422.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___339_422.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___339_422.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___339_422.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___339_422.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___339_422.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___339_422.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___339_422.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___339_422.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___339_422.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___339_422.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___339_422.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___339_422.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___339_422.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___339_422.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___339_422.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___339_422.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___339_422.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___339_422.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___339_422.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___339_422.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___339_422.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___339_422.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___339_422.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___339_422.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___339_422.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___339_422.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___339_422.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___339_422.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___339_422.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___339_422.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___339_422.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___339_422.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___339_422.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___339_422.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___339_422.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___339_422.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___339_422.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____424 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____424 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____461 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____491 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____516 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____522 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____528 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___306_543  ->
    match uu___306_543 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____549 = FStar_Syntax_Util.head_and_args t  in
    match uu____549 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____610 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____611 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____623 =
                     let uu____624 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____624  in
                   FStar_Util.format1 "@<%s>" uu____623
                in
             let uu____627 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____610 uu____611 uu____627
         | uu____628 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___307_638  ->
      match uu___307_638 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____642 =
            let uu____645 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____646 =
              let uu____649 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____650 =
                let uu____653 =
                  let uu____656 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____656]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____653
                 in
              uu____649 :: uu____650  in
            uu____645 :: uu____646  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____642
      | FStar_TypeChecker_Common.CProb p ->
          let uu____660 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____661 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____662 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____660 uu____661
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____662
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___308_672  ->
      match uu___308_672 with
      | UNIV (u,t) ->
          let x =
            let uu____676 = FStar_Options.hide_uvar_nums ()  in
            if uu____676
            then "?"
            else
              (let uu____678 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____678 FStar_Util.string_of_int)
             in
          let uu____679 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____679
      | TERM (u,t) ->
          let x =
            let uu____683 = FStar_Options.hide_uvar_nums ()  in
            if uu____683
            then "?"
            else
              (let uu____685 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____685 FStar_Util.string_of_int)
             in
          let uu____686 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____686
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____701 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____701 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____715 =
      let uu____718 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____718
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____715 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____731 .
    (FStar_Syntax_Syntax.term,'Auu____731) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____749 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____767  ->
              match uu____767 with
              | (x,uu____773) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____749 (FStar_String.concat " ")
  
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
        (let uu____803 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____803
         then
           let uu____804 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____804
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___309_810  ->
    match uu___309_810 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____815 .
    'Auu____815 FStar_TypeChecker_Common.problem ->
      'Auu____815 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___340_827 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___340_827.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___340_827.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___340_827.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___340_827.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___340_827.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___340_827.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___340_827.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____834 .
    'Auu____834 FStar_TypeChecker_Common.problem ->
      'Auu____834 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___310_851  ->
    match uu___310_851 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___311_866  ->
    match uu___311_866 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___341_872 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___341_872.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___341_872.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___341_872.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___341_872.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___341_872.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___341_872.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___341_872.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___341_872.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___341_872.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___342_880 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___342_880.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___342_880.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___342_880.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___342_880.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___342_880.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___342_880.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___342_880.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___342_880.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___342_880.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___312_892  ->
      match uu___312_892 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___313_897  ->
    match uu___313_897 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___314_908  ->
    match uu___314_908 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___315_921  ->
    match uu___315_921 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___316_934  ->
    match uu___316_934 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___317_947  ->
    match uu___317_947 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___318_960  ->
    match uu___318_960 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___319_971  ->
    match uu___319_971 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____986 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____986) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1014 =
          let uu____1015 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1015  in
        if uu____1014
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1049)::bs ->
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
          let uu____1095 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1119 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1119]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1095
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1147 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1171 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1171]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1147
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1214 =
          let uu____1215 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1215  in
        if uu____1214
        then ()
        else
          (let uu____1217 =
             let uu____1220 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1220
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1217 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1266 =
          let uu____1267 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1267  in
        if uu____1266
        then ()
        else
          (let uu____1269 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1269)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1286 =
        let uu____1287 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1287  in
      if uu____1286
      then ()
      else
        (let msgf m =
           let uu____1295 =
             let uu____1296 =
               let uu____1297 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1297 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1296  in
           Prims.strcat msg uu____1295  in
         (let uu____1299 = msgf "scope"  in
          let uu____1300 = p_scope prob  in
          def_scope_wf uu____1299 (p_loc prob) uu____1300);
         (let uu____1312 = msgf "guard"  in
          def_check_scoped uu____1312 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1317 = msgf "lhs"  in
                def_check_scoped uu____1317 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1318 = msgf "rhs"  in
                def_check_scoped uu____1318 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1323 = msgf "lhs"  in
                def_check_scoped_comp uu____1323 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1324 = msgf "rhs"  in
                def_check_scoped_comp uu____1324 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___343_1340 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___343_1340.wl_deferred);
          ctr = (uu___343_1340.ctr);
          defer_ok = (uu___343_1340.defer_ok);
          smt_ok;
          tcenv = (uu___343_1340.tcenv);
          wl_implicits = (uu___343_1340.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1347 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1347,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___344_1370 = empty_worklist env  in
      let uu____1371 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1371;
        wl_deferred = (uu___344_1370.wl_deferred);
        ctr = (uu___344_1370.ctr);
        defer_ok = (uu___344_1370.defer_ok);
        smt_ok = (uu___344_1370.smt_ok);
        tcenv = (uu___344_1370.tcenv);
        wl_implicits = (uu___344_1370.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___345_1391 = wl  in
        {
          attempting = (uu___345_1391.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___345_1391.ctr);
          defer_ok = (uu___345_1391.defer_ok);
          smt_ok = (uu___345_1391.smt_ok);
          tcenv = (uu___345_1391.tcenv);
          wl_implicits = (uu___345_1391.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___346_1413 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___346_1413.wl_deferred);
         ctr = (uu___346_1413.ctr);
         defer_ok = (uu___346_1413.defer_ok);
         smt_ok = (uu___346_1413.smt_ok);
         tcenv = (uu___346_1413.tcenv);
         wl_implicits = (uu___346_1413.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1424 .
    worklist ->
      'Auu____1424 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1453 = FStar_Syntax_Util.type_u ()  in
          match uu____1453 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1465 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1465 with
               | (uu____1476,tt,wl1) ->
                   let uu____1479 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1479, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___320_1484  ->
    match uu___320_1484 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1500 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1500 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1510  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1604 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1604 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1604 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1604 FStar_TypeChecker_Common.problem,worklist)
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
                        let uu____1689 =
                          let uu____1698 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1698]  in
                        FStar_List.append scope uu____1689
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____1741 =
                      let uu____1744 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____1744  in
                    FStar_List.append uu____1741
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____1763 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1763 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____1782 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____1782;
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
                  (let uu____1850 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1850 with
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
                  (let uu____1933 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1933 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____1969 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1969 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1969 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____1969 FStar_TypeChecker_Common.problem,worklist)
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
                          let uu____2035 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2035]  in
                        let uu____2054 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2054
                     in
                  let uu____2057 =
                    let uu____2064 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___347_2074 = wl  in
                       {
                         attempting = (uu___347_2074.attempting);
                         wl_deferred = (uu___347_2074.wl_deferred);
                         ctr = (uu___347_2074.ctr);
                         defer_ok = (uu___347_2074.defer_ok);
                         smt_ok = (uu___347_2074.smt_ok);
                         tcenv = env;
                         wl_implicits = (uu___347_2074.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2064
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2057 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2086 =
                              let uu____2091 =
                                let uu____2092 =
                                  let uu____2101 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2101
                                   in
                                [uu____2092]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2091  in
                            uu____2086 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2131 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2131;
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
                let uu____2173 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2173;
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
  'Auu____2185 .
    worklist ->
      'Auu____2185 FStar_TypeChecker_Common.problem ->
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
              let uu____2218 =
                let uu____2221 =
                  let uu____2222 =
                    let uu____2229 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2229)  in
                  FStar_Syntax_Syntax.NT uu____2222  in
                [uu____2221]  in
              FStar_Syntax_Subst.subst uu____2218 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2249 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2249
        then
          let uu____2250 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2251 = prob_to_string env d  in
          let uu____2252 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2250 uu____2251 uu____2252 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2258 -> failwith "impossible"  in
           let uu____2259 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2271 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2272 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2271, uu____2272)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2276 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2277 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2276, uu____2277)
              in
           match uu____2259 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___321_2295  ->
            match uu___321_2295 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2307 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2311 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2311 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___322_2340  ->
           match uu___322_2340 with
           | UNIV uu____2343 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2350 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2350
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
        (fun uu___323_2374  ->
           match uu___323_2374 with
           | UNIV (u',t) ->
               let uu____2379 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2379
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2383 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2394 =
        let uu____2395 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF] env uu____2395
         in
      FStar_Syntax_Subst.compress uu____2394
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2406 =
        FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
          env t
         in
      FStar_Syntax_Subst.compress uu____2406
  
let norm_arg :
  'Auu____2413 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2413) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2413)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2436 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2436, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2487  ->
              match uu____2487 with
              | (x,imp) ->
                  let uu____2506 =
                    let uu___348_2507 = x  in
                    let uu____2508 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___348_2507.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___348_2507.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2508
                    }  in
                  (uu____2506, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2531 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2531
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2535 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2535
        | uu____2538 -> u2  in
      let uu____2539 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2539
  
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
                (let uu____2661 = norm_refinement env t12  in
                 match uu____2661 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2678;
                     FStar_Syntax_Syntax.vars = uu____2679;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2705 =
                       let uu____2706 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2707 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2706 uu____2707
                        in
                     failwith uu____2705)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2723 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2723
          | FStar_Syntax_Syntax.Tm_uinst uu____2724 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2763 =
                   let uu____2764 = FStar_Syntax_Subst.compress t1'  in
                   uu____2764.FStar_Syntax_Syntax.n  in
                 match uu____2763 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2781 -> aux true t1'
                 | uu____2788 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2805 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2838 =
                   let uu____2839 = FStar_Syntax_Subst.compress t1'  in
                   uu____2839.FStar_Syntax_Syntax.n  in
                 match uu____2838 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2856 -> aux true t1'
                 | uu____2863 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2880 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2929 =
                   let uu____2930 = FStar_Syntax_Subst.compress t1'  in
                   uu____2930.FStar_Syntax_Syntax.n  in
                 match uu____2929 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2947 -> aux true t1'
                 | uu____2954 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2971 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2988 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3005 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3022 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3039 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3070 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3105 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3128 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3157 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3186 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3225 ->
              let uu____3232 =
                let uu____3233 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3234 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3233 uu____3234
                 in
              failwith uu____3232
          | FStar_Syntax_Syntax.Tm_ascribed uu____3249 ->
              let uu____3276 =
                let uu____3277 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3278 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3277 uu____3278
                 in
              failwith uu____3276
          | FStar_Syntax_Syntax.Tm_delayed uu____3293 ->
              let uu____3316 =
                let uu____3317 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3318 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3317 uu____3318
                 in
              failwith uu____3316
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3333 =
                let uu____3334 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3335 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3334 uu____3335
                 in
              failwith uu____3333
           in
        let uu____3350 = whnf env t1  in aux false uu____3350
  
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
      let uu____3406 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3406 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3446 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3446, FStar_Syntax_Util.t_true)
  
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
        let uu____3470 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3470 with
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
  fun uu____3549  ->
    match uu____3549 with
    | (t_base,refopt) ->
        let uu____3580 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3580 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3618 =
      let uu____3621 =
        let uu____3624 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3647  ->
                  match uu____3647 with | (uu____3654,uu____3655,x) -> x))
           in
        FStar_List.append wl.attempting uu____3624  in
      FStar_List.map (wl_prob_to_string wl) uu____3621  in
    FStar_All.pipe_right uu____3618 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____3669 .
    ('Auu____3669,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3680  ->
    match uu____3680 with
    | (uu____3687,c,args) ->
        let uu____3690 = print_ctx_uvar c  in
        let uu____3691 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3690 uu____3691
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3697 = FStar_Syntax_Util.head_and_args t  in
    match uu____3697 with
    | (head1,_args) ->
        let uu____3740 =
          let uu____3741 = FStar_Syntax_Subst.compress head1  in
          uu____3741.FStar_Syntax_Syntax.n  in
        (match uu____3740 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3744 -> true
         | uu____3757 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3763 = FStar_Syntax_Util.head_and_args t  in
    match uu____3763 with
    | (head1,_args) ->
        let uu____3806 =
          let uu____3807 = FStar_Syntax_Subst.compress head1  in
          uu____3807.FStar_Syntax_Syntax.n  in
        (match uu____3806 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____3811) -> u
         | uu____3828 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____3851 = FStar_Syntax_Util.head_and_args t  in
      match uu____3851 with
      | (head1,args) ->
          let uu____3898 =
            let uu____3899 = FStar_Syntax_Subst.compress head1  in
            uu____3899.FStar_Syntax_Syntax.n  in
          (match uu____3898 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____3907)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____3940 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___324_3965  ->
                         match uu___324_3965 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____3969 =
                               let uu____3970 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____3970.FStar_Syntax_Syntax.n  in
                             (match uu____3969 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____3974 -> false)
                         | uu____3975 -> true))
                  in
               (match uu____3940 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____3999 =
                        FStar_List.collect
                          (fun uu___325_4011  ->
                             match uu___325_4011 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4015 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4015]
                             | uu____4016 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____3999 FStar_List.rev  in
                    let uu____4039 =
                      let uu____4046 =
                        let uu____4055 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___326_4077  ->
                                  match uu___326_4077 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4081 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4081]
                                  | uu____4082 -> []))
                           in
                        FStar_All.pipe_right uu____4055 FStar_List.rev  in
                      let uu____4105 =
                        let uu____4108 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4108  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4046 uu____4105
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4039 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4143  ->
                                match uu____4143 with
                                | (x,i) ->
                                    let uu____4162 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4162, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4193  ->
                                match uu____4193 with
                                | (a,i) ->
                                    let uu____4212 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4212, i)) args_sol
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
           | uu____4234 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4254 =
          let uu____4277 =
            let uu____4278 = FStar_Syntax_Subst.compress k  in
            uu____4278.FStar_Syntax_Syntax.n  in
          match uu____4277 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4359 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4359)
              else
                (let uu____4393 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4393 with
                 | (ys',t1,uu____4426) ->
                     let uu____4431 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4431))
          | uu____4470 ->
              let uu____4471 =
                let uu____4476 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4476)  in
              ((ys, t), uu____4471)
           in
        match uu____4254 with
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
                 let uu____4569 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4569 c  in
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
               (let uu____4643 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4643
                then
                  let uu____4644 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4645 = print_ctx_uvar uv  in
                  let uu____4646 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4644 uu____4645 uu____4646
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4652 =
                   let uu____4653 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4653  in
                 let uu____4654 =
                   let uu____4657 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4657
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____4652 uu____4654 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____4690 =
               let uu____4691 =
                 let uu____4692 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____4693 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____4692 uu____4693
                  in
               failwith uu____4691  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____4757  ->
                       match uu____4757 with
                       | (a,i) ->
                           let uu____4778 =
                             let uu____4779 = FStar_Syntax_Subst.compress a
                                in
                             uu____4779.FStar_Syntax_Syntax.n  in
                           (match uu____4778 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____4805 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____4815 =
                 let uu____4816 = is_flex g  in Prims.op_Negation uu____4816
                  in
               if uu____4815
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____4820 = destruct_flex_t g wl  in
                  match uu____4820 with
                  | ((uu____4825,uv1,args),wl1) ->
                      ((let uu____4830 = args_as_binders args  in
                        assign_solution uu____4830 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___349_4832 = wl1  in
              {
                attempting = (uu___349_4832.attempting);
                wl_deferred = (uu___349_4832.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___349_4832.defer_ok);
                smt_ok = (uu___349_4832.smt_ok);
                tcenv = (uu___349_4832.tcenv);
                wl_implicits = (uu___349_4832.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4853 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4853
         then
           let uu____4854 = FStar_Util.string_of_int pid  in
           let uu____4855 =
             let uu____4856 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4856 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4854 uu____4855
         else ());
        commit sol;
        (let uu___350_4863 = wl  in
         {
           attempting = (uu___350_4863.attempting);
           wl_deferred = (uu___350_4863.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___350_4863.defer_ok);
           smt_ok = (uu___350_4863.smt_ok);
           tcenv = (uu___350_4863.tcenv);
           wl_implicits = (uu___350_4863.wl_implicits)
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
             | (uu____4925,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4953 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4953
              in
           (let uu____4959 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4959
            then
              let uu____4960 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4961 =
                let uu____4962 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4962 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4960 uu____4961
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
        let uu____4987 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4987 FStar_Util.set_elements  in
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
      let uu____5021 = occurs uk t  in
      match uu____5021 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5050 =
                 let uu____5051 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5052 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5051 uu____5052
                  in
               FStar_Pervasives_Native.Some uu____5050)
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
            let uu____5165 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5165 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5215 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5271  ->
             match uu____5271 with
             | (x,uu____5283) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5300 = FStar_List.last bs  in
      match uu____5300 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5324) ->
          let uu____5335 =
            FStar_Util.prefix_until
              (fun uu___327_5350  ->
                 match uu___327_5350 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5352 -> false) g
             in
          (match uu____5335 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5365,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5401 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5401 with
        | (pfx,uu____5411) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5423 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5423 with
             | (uu____5430,src',wl1) ->
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
                 | uu____5542 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5543 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5607  ->
                  fun uu____5608  ->
                    match (uu____5607, uu____5608) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5711 =
                          let uu____5712 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5712
                           in
                        if uu____5711
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5741 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5741
                           then
                             let uu____5756 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5756)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5543 with | (isect,uu____5805) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5840 'Auu____5841 .
    (FStar_Syntax_Syntax.bv,'Auu____5840) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5841) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5898  ->
              fun uu____5899  ->
                match (uu____5898, uu____5899) with
                | ((a,uu____5917),(b,uu____5919)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5934 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5934) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5964  ->
           match uu____5964 with
           | (y,uu____5970) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5979 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5979) FStar_Pervasives_Native.tuple2
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
                   let uu____6141 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6141
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6171 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6218 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6256 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6269 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___328_6274  ->
    match uu___328_6274 with
    | MisMatch (d1,d2) ->
        let uu____6285 =
          let uu____6286 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6287 =
            let uu____6288 =
              let uu____6289 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6289 ")"  in
            Prims.strcat ") (" uu____6288  in
          Prims.strcat uu____6286 uu____6287  in
        Prims.strcat "MisMatch (" uu____6285
    | HeadMatch u ->
        let uu____6291 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6291
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___329_6296  ->
    match uu___329_6296 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6311 -> HeadMatch false
  
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
          let uu____6325 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6325 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6336 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6359 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6368 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6394 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6394
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6395 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6396 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6397 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6410 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6423 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6447) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6453,uu____6454) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6496) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6521;
             FStar_Syntax_Syntax.index = uu____6522;
             FStar_Syntax_Syntax.sort = t2;_},uu____6524)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6531 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6532 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6533 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6548 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6555 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6575 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6575
  
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
            let uu____6602 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6602
            then FullMatch
            else
              (let uu____6604 =
                 let uu____6613 =
                   let uu____6616 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6616  in
                 let uu____6617 =
                   let uu____6620 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6620  in
                 (uu____6613, uu____6617)  in
               MisMatch uu____6604)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6626),FStar_Syntax_Syntax.Tm_uinst (g,uu____6628)) ->
            let uu____6637 = head_matches env f g  in
            FStar_All.pipe_right uu____6637 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6640 = FStar_Const.eq_const c d  in
            if uu____6640
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6647),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6649)) ->
            let uu____6682 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6682
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6689),FStar_Syntax_Syntax.Tm_refine (y,uu____6691)) ->
            let uu____6700 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6700 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6702),uu____6703) ->
            let uu____6708 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6708 head_match
        | (uu____6709,FStar_Syntax_Syntax.Tm_refine (x,uu____6711)) ->
            let uu____6716 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6716 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6717,FStar_Syntax_Syntax.Tm_type
           uu____6718) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6719,FStar_Syntax_Syntax.Tm_arrow uu____6720) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6750),FStar_Syntax_Syntax.Tm_app (head',uu____6752))
            ->
            let uu____6801 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6801 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6803),uu____6804) ->
            let uu____6829 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6829 head_match
        | (uu____6830,FStar_Syntax_Syntax.Tm_app (head1,uu____6832)) ->
            let uu____6857 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6857 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6858,FStar_Syntax_Syntax.Tm_let
           uu____6859) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6884,FStar_Syntax_Syntax.Tm_match uu____6885) ->
            HeadMatch true
        | uu____6930 ->
            let uu____6935 =
              let uu____6944 = delta_depth_of_term env t11  in
              let uu____6947 = delta_depth_of_term env t21  in
              (uu____6944, uu____6947)  in
            MisMatch uu____6935
  
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
          (let uu____7007 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7007
           then
             let uu____7008 = FStar_Syntax_Print.term_to_string t  in
             let uu____7009 = FStar_Syntax_Print.term_to_string head1  in
             FStar_Util.print2 "Head of %s is %s\n" uu____7008 uu____7009
           else ());
          (let uu____7011 =
             let uu____7012 = FStar_Syntax_Util.un_uinst head1  in
             uu____7012.FStar_Syntax_Syntax.n  in
           match uu____7011 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____7018 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant;
                   FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____7018 with
                | FStar_Pervasives_Native.None  ->
                    ((let uu____7032 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7032
                      then
                        let uu____7033 =
                          FStar_Syntax_Print.term_to_string head1  in
                        FStar_Util.print1 "No definition found for %s\n"
                          uu____7033
                      else ());
                     FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.Some uu____7035 ->
                    let t' =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota] env t
                       in
                    ((let uu____7046 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7046
                      then
                        let uu____7047 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____7048 = FStar_Syntax_Print.term_to_string t'
                           in
                        FStar_Util.print2 "Inlined %s to %s\n" uu____7047
                          uu____7048
                      else ());
                     FStar_Pervasives_Native.Some t'))
           | uu____7050 -> FStar_Pervasives_Native.None)
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
          (let uu____7188 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7188
           then
             let uu____7189 = FStar_Syntax_Print.term_to_string t11  in
             let uu____7190 = FStar_Syntax_Print.term_to_string t21  in
             let uu____7191 = string_of_match_result r  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7189
               uu____7190 uu____7191
           else ());
          (let reduce_one_and_try_again d1 d2 =
             let d1_greater_than_d2 =
               FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
             let uu____7215 =
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
             match uu____7215 with
             | (t12,t22) ->
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           let reduce_both_and_try_again d r1 =
             let uu____7260 = FStar_TypeChecker_Common.decr_delta_depth d  in
             match uu____7260 with
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
                uu____7292),uu____7293)
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7311 =
                    let uu____7320 = maybe_inline t11  in
                    let uu____7323 = maybe_inline t21  in
                    (uu____7320, uu____7323)  in
                  match uu____7311 with
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
               (uu____7360,FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level uu____7361))
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7379 =
                    let uu____7388 = maybe_inline t11  in
                    let uu____7391 = maybe_inline t21  in
                    (uu____7388, uu____7391)  in
                  match uu____7379 with
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
           | MisMatch uu____7440 -> fail1 n_delta r t11 t21
           | uu____7449 -> success n_delta r t11 t21)
           in
        let r = aux true (Prims.parse_int "0") t1 t2  in
        (let uu____7462 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelDelta")
            in
         if uu____7462
         then
           let uu____7463 = FStar_Syntax_Print.term_to_string t1  in
           let uu____7464 = FStar_Syntax_Print.term_to_string t2  in
           let uu____7465 =
             string_of_match_result (FStar_Pervasives_Native.fst r)  in
           let uu____7472 =
             if
               (FStar_Pervasives_Native.snd r) = FStar_Pervasives_Native.None
             then "None"
             else
               (let uu____7490 =
                  FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____7490
                  (fun uu____7524  ->
                     match uu____7524 with
                     | (t11,t21) ->
                         let uu____7531 =
                           FStar_Syntax_Print.term_to_string t11  in
                         let uu____7532 =
                           let uu____7533 =
                             FStar_Syntax_Print.term_to_string t21  in
                           Prims.strcat "; " uu____7533  in
                         Prims.strcat uu____7531 uu____7532))
              in
           FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
             uu____7463 uu____7464 uu____7465 uu____7472
         else ());
        r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7545 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7545 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___330_7558  ->
    match uu___330_7558 with
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
      let uu___351_7595 = p  in
      let uu____7598 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7599 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___351_7595.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7598;
        FStar_TypeChecker_Common.relation =
          (uu___351_7595.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7599;
        FStar_TypeChecker_Common.element =
          (uu___351_7595.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___351_7595.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___351_7595.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___351_7595.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___351_7595.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___351_7595.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7613 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7613
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7618 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7640 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7640 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7648 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7648 with
           | (lh,lhs_args) ->
               let uu____7695 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7695 with
                | (rh,rhs_args) ->
                    let uu____7742 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7755,FStar_Syntax_Syntax.Tm_uvar uu____7756)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7845 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7872,uu____7873)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7888,FStar_Syntax_Syntax.Tm_uvar uu____7889)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7904,FStar_Syntax_Syntax.Tm_arrow uu____7905)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___352_7935 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___352_7935.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___352_7935.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___352_7935.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___352_7935.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___352_7935.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___352_7935.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___352_7935.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___352_7935.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___352_7935.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7938,FStar_Syntax_Syntax.Tm_type uu____7939)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___352_7955 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___352_7955.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___352_7955.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___352_7955.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___352_7955.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___352_7955.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___352_7955.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___352_7955.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___352_7955.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___352_7955.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7958,FStar_Syntax_Syntax.Tm_uvar uu____7959)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___352_7975 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___352_7975.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___352_7975.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___352_7975.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___352_7975.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___352_7975.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___352_7975.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___352_7975.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___352_7975.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___352_7975.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7978,FStar_Syntax_Syntax.Tm_uvar uu____7979)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7994,uu____7995)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8010,FStar_Syntax_Syntax.Tm_uvar uu____8011)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8026,uu____8027) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7742 with
                     | (rank,tp1) ->
                         let uu____8040 =
                           FStar_All.pipe_right
                             (let uu___353_8044 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___353_8044.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___353_8044.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___353_8044.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___353_8044.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___353_8044.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___353_8044.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___353_8044.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___353_8044.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___353_8044.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____8040))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8050 =
            FStar_All.pipe_right
              (let uu___354_8054 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___354_8054.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___354_8054.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___354_8054.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___354_8054.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___354_8054.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___354_8054.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___354_8054.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___354_8054.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___354_8054.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8050)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8115 probs =
      match uu____8115 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8196 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8217 = rank wl.tcenv hd1  in
               (match uu____8217 with
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
                      (let uu____8276 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8280 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8280)
                          in
                       if uu____8276
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
          let uu____8348 = FStar_Syntax_Util.head_and_args t  in
          match uu____8348 with
          | (hd1,uu____8366) ->
              let uu____8391 =
                let uu____8392 = FStar_Syntax_Subst.compress hd1  in
                uu____8392.FStar_Syntax_Syntax.n  in
              (match uu____8391 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8396) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8430  ->
                           match uu____8430 with
                           | (y,uu____8438) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8460  ->
                                       match uu____8460 with
                                       | (x,uu____8468) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8473 -> false)
           in
        let uu____8474 = rank tcenv p  in
        match uu____8474 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8481 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8508 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8522 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8536 -> false
  
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
                        let uu____8588 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8588 with
                        | (k,uu____8594) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8604 -> false)))
            | uu____8605 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8657 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8663 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8663 = (Prims.parse_int "0")))
                           in
                        if uu____8657 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8679 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8685 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8685 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8679)
               in
            let uu____8686 = filter1 u12  in
            let uu____8689 = filter1 u22  in (uu____8686, uu____8689)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8718 = filter_out_common_univs us1 us2  in
                (match uu____8718 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8777 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8777 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8780 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8790 =
                          let uu____8791 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8792 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8791
                            uu____8792
                           in
                        UFailed uu____8790))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8816 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8816 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8842 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8842 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8845 ->
                let uu____8850 =
                  let uu____8851 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8852 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8851
                    uu____8852 msg
                   in
                UFailed uu____8850
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8853,uu____8854) ->
              let uu____8855 =
                let uu____8856 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8857 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8856 uu____8857
                 in
              failwith uu____8855
          | (FStar_Syntax_Syntax.U_unknown ,uu____8858) ->
              let uu____8859 =
                let uu____8860 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8861 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8860 uu____8861
                 in
              failwith uu____8859
          | (uu____8862,FStar_Syntax_Syntax.U_bvar uu____8863) ->
              let uu____8864 =
                let uu____8865 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8866 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8865 uu____8866
                 in
              failwith uu____8864
          | (uu____8867,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8868 =
                let uu____8869 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8870 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8869 uu____8870
                 in
              failwith uu____8868
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8894 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8894
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8908 = occurs_univ v1 u3  in
              if uu____8908
              then
                let uu____8909 =
                  let uu____8910 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8911 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8910 uu____8911
                   in
                try_umax_components u11 u21 uu____8909
              else
                (let uu____8913 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8913)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8925 = occurs_univ v1 u3  in
              if uu____8925
              then
                let uu____8926 =
                  let uu____8927 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8928 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8927 uu____8928
                   in
                try_umax_components u11 u21 uu____8926
              else
                (let uu____8930 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8930)
          | (FStar_Syntax_Syntax.U_max uu____8931,uu____8932) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8938 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8938
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8940,FStar_Syntax_Syntax.U_max uu____8941) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8947 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8947
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8949,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8950,FStar_Syntax_Syntax.U_name
             uu____8951) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8952) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8953) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8954,FStar_Syntax_Syntax.U_succ
             uu____8955) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8956,FStar_Syntax_Syntax.U_zero
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
      let uu____9056 = bc1  in
      match uu____9056 with
      | (bs1,mk_cod1) ->
          let uu____9100 = bc2  in
          (match uu____9100 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9211 = aux xs ys  in
                     (match uu____9211 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9294 =
                       let uu____9301 = mk_cod1 xs  in ([], uu____9301)  in
                     let uu____9304 =
                       let uu____9311 = mk_cod2 ys  in ([], uu____9311)  in
                     (uu____9294, uu____9304)
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
                  let uu____9379 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9379 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9382 =
                    let uu____9383 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9383 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9382
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9388 = has_type_guard t1 t2  in (uu____9388, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9389 = has_type_guard t2 t1  in (uu____9389, wl)
  
let is_flex_pat :
  'Auu____9398 'Auu____9399 'Auu____9400 .
    ('Auu____9398,'Auu____9399,'Auu____9400 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___331_9413  ->
    match uu___331_9413 with
    | (uu____9422,uu____9423,[]) -> true
    | uu____9426 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9457 = f  in
      match uu____9457 with
      | (uu____9464,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9465;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9466;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9469;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9470;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9471;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9531  ->
                 match uu____9531 with
                 | (y,uu____9539) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9693 =
                  let uu____9708 =
                    let uu____9711 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9711  in
                  ((FStar_List.rev pat_binders), uu____9708)  in
                FStar_Pervasives_Native.Some uu____9693
            | (uu____9744,[]) ->
                let uu____9775 =
                  let uu____9790 =
                    let uu____9793 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9793  in
                  ((FStar_List.rev pat_binders), uu____9790)  in
                FStar_Pervasives_Native.Some uu____9775
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9884 =
                  let uu____9885 = FStar_Syntax_Subst.compress a  in
                  uu____9885.FStar_Syntax_Syntax.n  in
                (match uu____9884 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9905 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9905
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___355_9932 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___355_9932.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___355_9932.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9936 =
                            let uu____9937 =
                              let uu____9944 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9944)  in
                            FStar_Syntax_Syntax.NT uu____9937  in
                          [uu____9936]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___356_9960 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___356_9960.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___356_9960.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9961 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____10001 =
                  let uu____10016 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10016  in
                (match uu____10001 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10091 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10124 ->
               let uu____10125 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10125 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10409 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10409
       then
         let uu____10410 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10410
       else ());
      (let uu____10412 = next_prob probs  in
       match uu____10412 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___357_10439 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___357_10439.wl_deferred);
               ctr = (uu___357_10439.ctr);
               defer_ok = (uu___357_10439.defer_ok);
               smt_ok = (uu___357_10439.smt_ok);
               tcenv = (uu___357_10439.tcenv);
               wl_implicits = (uu___357_10439.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10447 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10447
                 then
                   let uu____10448 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10448
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
                           (let uu___358_10453 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___358_10453.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___358_10453.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___358_10453.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___358_10453.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___358_10453.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___358_10453.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___358_10453.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___358_10453.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___358_10453.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10475 ->
                let uu____10484 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10543  ->
                          match uu____10543 with
                          | (c,uu____10551,uu____10552) -> c < probs.ctr))
                   in
                (match uu____10484 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10593 =
                            let uu____10598 =
                              FStar_List.map
                                (fun uu____10613  ->
                                   match uu____10613 with
                                   | (uu____10624,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10598, (probs.wl_implicits))  in
                          Success uu____10593
                      | uu____10627 ->
                          let uu____10636 =
                            let uu___359_10637 = probs  in
                            let uu____10638 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10657  ->
                                      match uu____10657 with
                                      | (uu____10664,uu____10665,y) -> y))
                               in
                            {
                              attempting = uu____10638;
                              wl_deferred = rest;
                              ctr = (uu___359_10637.ctr);
                              defer_ok = (uu___359_10637.defer_ok);
                              smt_ok = (uu___359_10637.smt_ok);
                              tcenv = (uu___359_10637.tcenv);
                              wl_implicits = (uu___359_10637.wl_implicits)
                            }  in
                          solve env uu____10636))))

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
            let uu____10672 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10672 with
            | USolved wl1 ->
                let uu____10674 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10674
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
                  let uu____10726 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10726 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10729 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10741;
                  FStar_Syntax_Syntax.vars = uu____10742;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10745;
                  FStar_Syntax_Syntax.vars = uu____10746;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10758,uu____10759) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10766,FStar_Syntax_Syntax.Tm_uinst uu____10767) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10774 -> USolved wl

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
            ((let uu____10784 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10784
              then
                let uu____10785 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10785 msg
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
               let uu____10871 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10871 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10924 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10924
                then
                  let uu____10925 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10926 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10925 uu____10926
                else ());
               (let uu____10928 = head_matches_delta env1 t1 t2  in
                match uu____10928 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10973 = eq_prob t1 t2 wl2  in
                         (match uu____10973 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____10994 ->
                         let uu____11003 = eq_prob t1 t2 wl2  in
                         (match uu____11003 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11052 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11067 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11068 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11067, uu____11068)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11073 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11074 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11073, uu____11074)
                            in
                         (match uu____11052 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11105 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11105 with
                                | (t1_hd,t1_args) ->
                                    let uu____11150 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11150 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11214 =
                                              let uu____11221 =
                                                let uu____11232 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11232 :: t1_args  in
                                              let uu____11249 =
                                                let uu____11258 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11258 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11307  ->
                                                   fun uu____11308  ->
                                                     fun uu____11309  ->
                                                       match (uu____11307,
                                                               uu____11308,
                                                               uu____11309)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11359),
                                                          (a2,uu____11361))
                                                           ->
                                                           let uu____11398 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11398
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11221
                                                uu____11249
                                               in
                                            match uu____11214 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___360_11424 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___360_11424.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___360_11424.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11432 =
                                                  solve env1 wl'  in
                                                (match uu____11432 with
                                                 | Success (uu____11435,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___361_11439
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___361_11439.attempting);
                                                            wl_deferred =
                                                              (uu___361_11439.wl_deferred);
                                                            ctr =
                                                              (uu___361_11439.ctr);
                                                            defer_ok =
                                                              (uu___361_11439.defer_ok);
                                                            smt_ok =
                                                              (uu___361_11439.smt_ok);
                                                            tcenv =
                                                              (uu___361_11439.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11440 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11472 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11472 with
                                | (t1_base,p1_opt) ->
                                    let uu____11519 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11519 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11629 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11629
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
                                               let uu____11677 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11677
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
                                               let uu____11707 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11707
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
                                               let uu____11737 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11737
                                           | uu____11740 -> t_base  in
                                         let uu____11757 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11757 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11771 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11771, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11778 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11778 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11825 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11825 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11872 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11872
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
                              let uu____11896 = combine t11 t21 wl2  in
                              (match uu____11896 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11929 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11929
                                     then
                                       let uu____11930 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11930
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11969 ts1 =
               match uu____11969 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12032 = pairwise out t wl2  in
                        (match uu____12032 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12068 =
               let uu____12079 = FStar_List.hd ts  in (uu____12079, [], wl1)
                in
             let uu____12088 = FStar_List.tl ts  in
             aux uu____12068 uu____12088  in
           let uu____12095 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12095 with
           | (this_flex,this_rigid) ->
               let uu____12119 =
                 let uu____12120 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12120.FStar_Syntax_Syntax.n  in
               (match uu____12119 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12145 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12145
                    then
                      let uu____12146 = destruct_flex_t this_flex wl  in
                      (match uu____12146 with
                       | (flex,wl1) ->
                           let uu____12153 = quasi_pattern env flex  in
                           (match uu____12153 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12171 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12171
                                  then
                                    let uu____12172 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12172
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12175 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___362_12178 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___362_12178.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___362_12178.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___362_12178.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___362_12178.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___362_12178.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___362_12178.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___362_12178.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___362_12178.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___362_12178.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12175)
                | uu____12179 ->
                    ((let uu____12181 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12181
                      then
                        let uu____12182 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12182
                      else ());
                     (let uu____12184 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12184 with
                      | (u,_args) ->
                          let uu____12227 =
                            let uu____12228 = FStar_Syntax_Subst.compress u
                               in
                            uu____12228.FStar_Syntax_Syntax.n  in
                          (match uu____12227 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12255 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12255 with
                                 | (u',uu____12273) ->
                                     let uu____12298 =
                                       let uu____12299 = whnf env u'  in
                                       uu____12299.FStar_Syntax_Syntax.n  in
                                     (match uu____12298 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12320 -> false)
                                  in
                               let uu____12321 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___332_12344  ->
                                         match uu___332_12344 with
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
                                              | uu____12353 -> false)
                                         | uu____12356 -> false))
                                  in
                               (match uu____12321 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12370 = whnf env this_rigid
                                         in
                                      let uu____12371 =
                                        FStar_List.collect
                                          (fun uu___333_12377  ->
                                             match uu___333_12377 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12383 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12383]
                                             | uu____12385 -> [])
                                          bounds_probs
                                         in
                                      uu____12370 :: uu____12371  in
                                    let uu____12386 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12386 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12417 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12432 =
                                               let uu____12433 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12433.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12432 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12445 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12445)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12454 -> bound  in
                                           let uu____12455 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12455)  in
                                         (match uu____12417 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12484 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12484
                                                then
                                                  let wl'1 =
                                                    let uu___363_12486 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___363_12486.wl_deferred);
                                                      ctr =
                                                        (uu___363_12486.ctr);
                                                      defer_ok =
                                                        (uu___363_12486.defer_ok);
                                                      smt_ok =
                                                        (uu___363_12486.smt_ok);
                                                      tcenv =
                                                        (uu___363_12486.tcenv);
                                                      wl_implicits =
                                                        (uu___363_12486.wl_implicits)
                                                    }  in
                                                  let uu____12487 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12487
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12490 =
                                                  solve_t env eq_prob
                                                    (let uu___364_12492 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___364_12492.wl_deferred);
                                                       ctr =
                                                         (uu___364_12492.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___364_12492.smt_ok);
                                                       tcenv =
                                                         (uu___364_12492.tcenv);
                                                       wl_implicits =
                                                         (uu___364_12492.wl_implicits)
                                                     })
                                                   in
                                                match uu____12490 with
                                                | Success uu____12493 ->
                                                    let wl2 =
                                                      let uu___365_12499 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___365_12499.wl_deferred);
                                                        ctr =
                                                          (uu___365_12499.ctr);
                                                        defer_ok =
                                                          (uu___365_12499.defer_ok);
                                                        smt_ok =
                                                          (uu___365_12499.smt_ok);
                                                        tcenv =
                                                          (uu___365_12499.tcenv);
                                                        wl_implicits =
                                                          (uu___365_12499.wl_implicits)
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
                                                    let uu____12514 =
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
                                                    ((let uu____12525 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12525
                                                      then
                                                        let uu____12526 =
                                                          let uu____12527 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12527
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12526
                                                      else ());
                                                     (let uu____12533 =
                                                        let uu____12548 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12548)
                                                         in
                                                      match uu____12533 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12570))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12596 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12596
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
                                                                  let uu____12613
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12613))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12638 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12638
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
                                                                    let uu____12656
                                                                    =
                                                                    let uu____12661
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12661
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12656
                                                                    [] wl2
                                                                     in
                                                                  let uu____12666
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12666))))
                                                      | uu____12667 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12682 when flip ->
                               let uu____12683 =
                                 let uu____12684 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12685 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12684 uu____12685
                                  in
                               failwith uu____12683
                           | uu____12686 ->
                               let uu____12687 =
                                 let uu____12688 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12689 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12688 uu____12689
                                  in
                               failwith uu____12687)))))

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
                      (fun uu____12723  ->
                         match uu____12723 with
                         | (x,i) ->
                             let uu____12742 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12742, i)) bs_lhs
                     in
                  let uu____12745 = lhs  in
                  match uu____12745 with
                  | (uu____12746,u_lhs,uu____12748) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12845 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12855 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12855, univ)
                             in
                          match uu____12845 with
                          | (k,univ) ->
                              let uu____12862 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12862 with
                               | (uu____12879,u,wl3) ->
                                   let uu____12882 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12882, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12908 =
                              let uu____12921 =
                                let uu____12932 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12932 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12983  ->
                                   fun uu____12984  ->
                                     match (uu____12983, uu____12984) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13085 =
                                           let uu____13092 =
                                             let uu____13095 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13095
                                              in
                                           copy_uvar u_lhs [] uu____13092 wl2
                                            in
                                         (match uu____13085 with
                                          | (uu____13124,t_a,wl3) ->
                                              let uu____13127 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13127 with
                                               | (uu____13146,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12921
                                ([], wl1)
                               in
                            (match uu____12908 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___366_13202 = ct  in
                                   let uu____13203 =
                                     let uu____13206 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13206
                                      in
                                   let uu____13221 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___366_13202.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___366_13202.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13203;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13221;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___366_13202.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___367_13239 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___367_13239.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___367_13239.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13242 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13242 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13304 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13304 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13315 =
                                          let uu____13320 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13320)  in
                                        TERM uu____13315  in
                                      let uu____13321 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13321 with
                                       | (sub_prob,wl3) ->
                                           let uu____13334 =
                                             let uu____13335 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13335
                                              in
                                           solve env uu____13334))
                             | (x,imp)::formals2 ->
                                 let uu____13357 =
                                   let uu____13364 =
                                     let uu____13367 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13367
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13364 wl1
                                    in
                                 (match uu____13357 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13388 =
                                          let uu____13391 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13391
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13388 u_x
                                         in
                                      let uu____13392 =
                                        let uu____13395 =
                                          let uu____13398 =
                                            let uu____13399 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13399, imp)  in
                                          [uu____13398]  in
                                        FStar_List.append bs_terms
                                          uu____13395
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13392 formals2 wl2)
                              in
                           let uu____13426 = occurs_check u_lhs arrow1  in
                           (match uu____13426 with
                            | (uu____13437,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13448 =
                                    let uu____13449 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13449
                                     in
                                  giveup_or_defer env orig wl uu____13448
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
              (let uu____13478 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13478
               then
                 let uu____13479 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13480 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13479 (rel_to_string (p_rel orig)) uu____13480
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13601 = rhs wl1 scope env1 subst1  in
                     (match uu____13601 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13621 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13621
                            then
                              let uu____13622 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13622
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___368_13698 = hd1  in
                       let uu____13699 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___368_13698.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___368_13698.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13699
                       }  in
                     let hd21 =
                       let uu___369_13703 = hd2  in
                       let uu____13704 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___369_13703.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___369_13703.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13704
                       }  in
                     let uu____13707 =
                       let uu____13712 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13712
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13707 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13731 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13731
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13735 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13735 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13798 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13798
                                  in
                               ((let uu____13816 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13816
                                 then
                                   let uu____13817 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13818 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13817
                                     uu____13818
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13845 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13878 = aux wl [] env [] bs1 bs2  in
               match uu____13878 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13927 = attempt sub_probs wl2  in
                   solve env uu____13927)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13932 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13932 wl)

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
              let uu____13946 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13946 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13980 = lhs1  in
              match uu____13980 with
              | (uu____13983,ctx_u,uu____13985) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13993 ->
                        let uu____13994 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13994 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____14041 = quasi_pattern env1 lhs1  in
              match uu____14041 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____14071) ->
                  let uu____14076 = lhs1  in
                  (match uu____14076 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____14090 = occurs_check ctx_u rhs1  in
                       (match uu____14090 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14132 =
                                let uu____14139 =
                                  let uu____14140 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14140
                                   in
                                FStar_Util.Inl uu____14139  in
                              (uu____14132, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14162 =
                                 let uu____14163 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14163  in
                               if uu____14162
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14183 =
                                    let uu____14190 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14190  in
                                  let uu____14195 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14183, uu____14195)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14263  ->
                     match uu____14263 with
                     | (x,i) ->
                         let uu____14282 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14282, i)) bs_lhs
                 in
              let uu____14285 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14285 with
              | (rhs_hd,args) ->
                  let uu____14328 = FStar_Util.prefix args  in
                  (match uu____14328 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14400 = lhs1  in
                       (match uu____14400 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14404 =
                              let uu____14415 =
                                let uu____14422 =
                                  let uu____14425 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14425
                                   in
                                copy_uvar u_lhs [] uu____14422 wl1  in
                              match uu____14415 with
                              | (uu____14452,t_last_arg,wl2) ->
                                  let uu____14455 =
                                    let uu____14462 =
                                      let uu____14463 =
                                        let uu____14472 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14472]  in
                                      FStar_List.append bs_lhs uu____14463
                                       in
                                    copy_uvar u_lhs uu____14462 t_res_lhs wl2
                                     in
                                  (match uu____14455 with
                                   | (uu____14507,lhs',wl3) ->
                                       let uu____14510 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14510 with
                                        | (uu____14527,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14404 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14548 =
                                     let uu____14549 =
                                       let uu____14554 =
                                         let uu____14555 =
                                           let uu____14558 =
                                             let uu____14563 =
                                               let uu____14564 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14564]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14563
                                              in
                                           uu____14558
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14555
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14554)  in
                                     TERM uu____14549  in
                                   [uu____14548]  in
                                 let uu____14591 =
                                   let uu____14598 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14598 with
                                   | (p1,wl3) ->
                                       let uu____14617 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14617 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14591 with
                                  | (sub_probs,wl3) ->
                                      let uu____14648 =
                                        let uu____14649 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14649  in
                                      solve env1 uu____14648))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14682 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14682 with
                | (uu____14699,args) ->
                    (match args with | [] -> false | uu____14733 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14750 =
                  let uu____14751 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14751.FStar_Syntax_Syntax.n  in
                match uu____14750 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14754 -> true
                | uu____14769 -> false  in
              let uu____14770 = quasi_pattern env1 lhs1  in
              match uu____14770 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14781 =
                    let uu____14782 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14782
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14781
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14789 = is_app rhs1  in
                  if uu____14789
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14791 = is_arrow rhs1  in
                     if uu____14791
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14793 =
                          let uu____14794 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14794
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14793))
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
                let uu____14797 = lhs  in
                (match uu____14797 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14801 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14801 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14818 =
                              let uu____14821 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14821
                               in
                            FStar_All.pipe_right uu____14818
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14838 = occurs_check ctx_uv rhs1  in
                          (match uu____14838 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14860 =
                                   let uu____14861 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14861
                                    in
                                 giveup_or_defer env orig wl uu____14860
                               else
                                 (let uu____14863 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14863
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14868 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14868
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14870 =
                                         let uu____14871 =
                                           names_to_string1 fvs2  in
                                         let uu____14872 =
                                           names_to_string1 fvs1  in
                                         let uu____14873 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14871 uu____14872
                                           uu____14873
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14870)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14881 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14885 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14885 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14908 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14908
                             | (FStar_Util.Inl msg,uu____14910) ->
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
                  (let uu____14943 =
                     let uu____14960 = quasi_pattern env lhs  in
                     let uu____14967 = quasi_pattern env rhs  in
                     (uu____14960, uu____14967)  in
                   match uu____14943 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____15010 = lhs  in
                       (match uu____15010 with
                        | ({ FStar_Syntax_Syntax.n = uu____15011;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____15013;_},u_lhs,uu____15015)
                            ->
                            let uu____15018 = rhs  in
                            (match uu____15018 with
                             | (uu____15019,u_rhs,uu____15021) ->
                                 let uu____15022 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____15022
                                 then
                                   let uu____15027 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____15027
                                 else
                                   (let uu____15029 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____15029 with
                                    | (sub_prob,wl1) ->
                                        let uu____15042 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____15042 with
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
                                             let uu____15074 =
                                               let uu____15081 =
                                                 let uu____15084 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____15084
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
                                                 uu____15081
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____15074 with
                                              | (uu____15087,w,wl2) ->
                                                  let w_app =
                                                    let uu____15093 =
                                                      let uu____15098 =
                                                        FStar_List.map
                                                          (fun uu____15109 
                                                             ->
                                                             match uu____15109
                                                             with
                                                             | (z,uu____15117)
                                                                 ->
                                                                 let uu____15122
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____15122)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____15098
                                                       in
                                                    uu____15093
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____15126 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____15126
                                                    then
                                                      let uu____15127 =
                                                        let uu____15130 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____15131 =
                                                          let uu____15134 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____15135 =
                                                            let uu____15138 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____15139 =
                                                              let uu____15142
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____15149
                                                                =
                                                                let uu____15152
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____15159
                                                                  =
                                                                  let uu____15162
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____15162]
                                                                   in
                                                                uu____15152
                                                                  ::
                                                                  uu____15159
                                                                 in
                                                              uu____15142 ::
                                                                uu____15149
                                                               in
                                                            uu____15138 ::
                                                              uu____15139
                                                             in
                                                          uu____15134 ::
                                                            uu____15135
                                                           in
                                                        uu____15130 ::
                                                          uu____15131
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____15127
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____15168 =
                                                          let uu____15173 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____15173)
                                                           in
                                                        TERM uu____15168  in
                                                      let uu____15174 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____15174
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____15179 =
                                                             let uu____15184
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
                                                               uu____15184)
                                                              in
                                                           TERM uu____15179
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____15185 =
                                                      let uu____15186 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____15186
                                                       in
                                                    solve env uu____15185)))))))
                   | uu____15187 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____15251 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15251
            then
              let uu____15252 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15253 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15254 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15255 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15252 uu____15253 uu____15254 uu____15255
            else ());
           (let uu____15258 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15258 with
            | (head1,args1) ->
                let uu____15301 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15301 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15365 =
                         let uu____15366 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15367 = args_to_string args1  in
                         let uu____15370 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15371 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15366 uu____15367 uu____15370 uu____15371
                          in
                       giveup env1 uu____15365 orig
                     else
                       (let uu____15375 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15381 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15381 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15375
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___370_15383 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___370_15383.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___370_15383.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___370_15383.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___370_15383.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___370_15383.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___370_15383.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___370_15383.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___370_15383.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____15385 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____15385 with
                              | USolved wl2 ->
                                  let uu____15387 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____15387
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____15391 = base_and_refinement env1 t1  in
                           match uu____15391 with
                           | (base1,refinement1) ->
                               let uu____15416 = base_and_refinement env1 t2
                                  in
                               (match uu____15416 with
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
                                           let uu____15536 =
                                             FStar_List.fold_right
                                               (fun uu____15576  ->
                                                  fun uu____15577  ->
                                                    match (uu____15576,
                                                            uu____15577)
                                                    with
                                                    | (((a1,uu____15629),
                                                        (a2,uu____15631)),
                                                       (probs,wl2)) ->
                                                        let uu____15680 =
                                                          let uu____15687 =
                                                            p_scope orig  in
                                                          mk_problem wl2
                                                            uu____15687 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15680
                                                         with
                                                         | (prob',wl3) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl3)))
                                               argp ([], wl1)
                                              in
                                           (match uu____15536 with
                                            | (subprobs,wl2) ->
                                                ((let uu____15719 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____15719
                                                  then
                                                    let uu____15720 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____15720
                                                  else ());
                                                 (let formula =
                                                    let uu____15725 =
                                                      FStar_List.map
                                                        (fun p  -> p_guard p)
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____15725
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  let uu____15733 =
                                                    attempt subprobs wl3  in
                                                  solve env1 uu____15733)))
                                         else
                                           (let uu____15735 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____15735 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let uu____15739 =
                                                  FStar_List.fold_right2
                                                    (fun uu____15776  ->
                                                       fun uu____15777  ->
                                                         fun uu____15778  ->
                                                           match (uu____15776,
                                                                   uu____15777,
                                                                   uu____15778)
                                                           with
                                                           | ((a,uu____15822),
                                                              (a',uu____15824),
                                                              (subprobs,wl3))
                                                               ->
                                                               let uu____15857
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 []
                                                                   orig a
                                                                   FStar_TypeChecker_Common.EQ
                                                                   a'
                                                                   FStar_Pervasives_Native.None
                                                                   "index"
                                                                  in
                                                               (match uu____15857
                                                                with
                                                                | (p,wl4) ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                    args1 args2 ([], wl2)
                                                   in
                                                (match uu____15739 with
                                                 | (subprobs,wl3) ->
                                                     ((let uu____15887 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           (FStar_Options.Other
                                                              "Rel")
                                                          in
                                                       if uu____15887
                                                       then
                                                         let uu____15888 =
                                                           FStar_Syntax_Print.list_to_string
                                                             (prob_to_string
                                                                env1)
                                                             subprobs
                                                            in
                                                         FStar_Util.print1
                                                           "Adding subproblems for arguments: %s\n"
                                                           uu____15888
                                                       else ());
                                                      FStar_List.iter
                                                        (def_check_prob
                                                           "solve_t' subprobs")
                                                        subprobs;
                                                      (let formula =
                                                         let uu____15894 =
                                                           FStar_List.map
                                                             p_guard subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____15894
                                                          in
                                                       let wl4 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl3
                                                          in
                                                       let uu____15902 =
                                                         attempt subprobs wl4
                                                          in
                                                       solve env1 uu____15902))))
                                     | uu____15903 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___371_15939 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___371_15939.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___371_15939.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___371_15939.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___371_15939.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___371_15939.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___371_15939.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___371_15939.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___371_15939.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16014 = destruct_flex_t scrutinee wl1  in
             match uu____16014 with
             | ((_t,uv,_args),wl2) ->
                 let tc_annot env2 t =
                   let uu____16040 =
                     env2.FStar_TypeChecker_Env.type_of
                       (let uu___372_16048 = env2  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___372_16048.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___372_16048.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___372_16048.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___372_16048.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___372_16048.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___372_16048.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___372_16048.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___372_16048.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___372_16048.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___372_16048.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___372_16048.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___372_16048.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___372_16048.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___372_16048.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___372_16048.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___372_16048.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___372_16048.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___372_16048.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___372_16048.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___372_16048.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___372_16048.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___372_16048.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___372_16048.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___372_16048.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___372_16048.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___372_16048.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___372_16048.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___372_16048.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___372_16048.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts = true;
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___372_16048.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___372_16048.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___372_16048.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___372_16048.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___372_16048.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___372_16048.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___372_16048.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___372_16048.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___372_16048.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___372_16048.FStar_TypeChecker_Env.dep_graph);
                          FStar_TypeChecker_Env.nbe =
                            (uu___372_16048.FStar_TypeChecker_Env.nbe)
                        }) t
                      in
                   match uu____16040 with | (t1,uu____16054,g) -> (t1, g)  in
                 let uu____16056 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p
                     tc_annot
                    in
                 (match uu____16056 with
                  | (xs,pat_term,uu____16071,uu____16072) ->
                      let uu____16077 =
                        FStar_List.fold_left
                          (fun uu____16100  ->
                             fun x  ->
                               match uu____16100 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____16121 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____16121 with
                                    | (uu____16140,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____16077 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____16161 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____16161 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___373_16177 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___373_16177.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    tcenv = (uu___373_16177.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____16185 = solve env1 wl'  in
                                (match uu____16185 with
                                 | Success (uu____16188,imps) ->
                                     let wl'1 =
                                       let uu___374_16191 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___374_16191.wl_deferred);
                                         ctr = (uu___374_16191.ctr);
                                         defer_ok = (uu___374_16191.defer_ok);
                                         smt_ok = (uu___374_16191.smt_ok);
                                         tcenv = (uu___374_16191.tcenv);
                                         wl_implicits =
                                           (uu___374_16191.wl_implicits)
                                       }  in
                                     let uu____16192 = solve env1 wl'1  in
                                     (match uu____16192 with
                                      | Success (uu____16195,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___375_16199 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___375_16199.attempting);
                                                 wl_deferred =
                                                   (uu___375_16199.wl_deferred);
                                                 ctr = (uu___375_16199.ctr);
                                                 defer_ok =
                                                   (uu___375_16199.defer_ok);
                                                 smt_ok =
                                                   (uu___375_16199.smt_ok);
                                                 tcenv =
                                                   (uu___375_16199.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16200 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16206 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16227 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16227
                 then
                   let uu____16228 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16229 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16228 uu____16229
                 else ());
                (let uu____16231 =
                   let uu____16252 =
                     let uu____16261 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16261)  in
                   let uu____16268 =
                     let uu____16277 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16277)  in
                   (uu____16252, uu____16268)  in
                 match uu____16231 with
                 | ((uu____16306,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16309;
                                   FStar_Syntax_Syntax.vars = uu____16310;_}),
                    (s,t)) ->
                     let uu____16381 =
                       let uu____16382 = is_flex scrutinee  in
                       Prims.op_Negation uu____16382  in
                     if uu____16381
                     then
                       ((let uu____16390 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16390
                         then
                           let uu____16391 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16391
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16403 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16403
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16409 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16409
                           then
                             let uu____16410 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16411 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16410 uu____16411
                           else ());
                          (let pat_discriminates uu___334_16432 =
                             match uu___334_16432 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16447;
                                  FStar_Syntax_Syntax.p = uu____16448;_},FStar_Pervasives_Native.None
                                ,uu____16449) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16462;
                                  FStar_Syntax_Syntax.p = uu____16463;_},FStar_Pervasives_Native.None
                                ,uu____16464) -> true
                             | uu____16489 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16589 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16589 with
                                       | (uu____16590,uu____16591,t') ->
                                           let uu____16609 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____16609 with
                                            | (FullMatch ,uu____16620) ->
                                                true
                                            | (HeadMatch
                                               uu____16633,uu____16634) ->
                                                true
                                            | uu____16647 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16680 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16680
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16685 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16685 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16773,uu____16774) ->
                                       branches1
                                   | uu____16919 -> branches  in
                                 let uu____16974 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____16983 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____16983 with
                                        | (p,uu____16987,uu____16988) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____16974))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17044 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17044 with
                                | (p,uu____17052,e) ->
                                    ((let uu____17071 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17071
                                      then
                                        let uu____17072 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17073 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17072 uu____17073
                                      else ());
                                     (let uu____17075 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____17075)))))
                 | ((s,t),(uu____17090,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____17093;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17094;_}))
                     ->
                     let uu____17163 =
                       let uu____17164 = is_flex scrutinee  in
                       Prims.op_Negation uu____17164  in
                     if uu____17163
                     then
                       ((let uu____17172 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____17172
                         then
                           let uu____17173 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17173
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17185 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17185
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17191 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17191
                           then
                             let uu____17192 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____17193 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17192 uu____17193
                           else ());
                          (let pat_discriminates uu___334_17214 =
                             match uu___334_17214 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17229;
                                  FStar_Syntax_Syntax.p = uu____17230;_},FStar_Pervasives_Native.None
                                ,uu____17231) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17244;
                                  FStar_Syntax_Syntax.p = uu____17245;_},FStar_Pervasives_Native.None
                                ,uu____17246) -> true
                             | uu____17271 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17371 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17371 with
                                       | (uu____17372,uu____17373,t') ->
                                           let uu____17391 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____17391 with
                                            | (FullMatch ,uu____17402) ->
                                                true
                                            | (HeadMatch
                                               uu____17415,uu____17416) ->
                                                true
                                            | uu____17429 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17462 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17462
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17467 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17467 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17555,uu____17556) ->
                                       branches1
                                   | uu____17701 -> branches  in
                                 let uu____17756 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17765 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17765 with
                                        | (p,uu____17769,uu____17770) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17756))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17826 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17826 with
                                | (p,uu____17834,e) ->
                                    ((let uu____17853 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17853
                                      then
                                        let uu____17854 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17855 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17854 uu____17855
                                      else ());
                                     (let uu____17857 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17857)))))
                 | uu____17870 ->
                     ((let uu____17892 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17892
                       then
                         let uu____17893 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17894 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17893 uu____17894
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____17935 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____17935
            then
              let uu____17936 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17937 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____17938 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17939 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____17936 uu____17937 uu____17938 uu____17939
            else ());
           (let uu____17941 = head_matches_delta env1 t1 t2  in
            match uu____17941 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____17972,uu____17973) ->
                     let rec may_relate head3 =
                       let uu____18000 =
                         let uu____18001 = FStar_Syntax_Subst.compress head3
                            in
                         uu____18001.FStar_Syntax_Syntax.n  in
                       match uu____18000 with
                       | FStar_Syntax_Syntax.Tm_name uu____18004 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18005 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18028;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____18029;
                             FStar_Syntax_Syntax.fv_qual = uu____18030;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18033;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____18034;
                             FStar_Syntax_Syntax.fv_qual = uu____18035;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____18039,uu____18040) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____18082) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____18088) ->
                           may_relate t
                       | uu____18093 -> false  in
                     let uu____18094 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____18094 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____18109 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____18109
                          then
                            let uu____18110 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____18110 with
                             | (guard,wl2) ->
                                 let uu____18117 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____18117)
                          else
                            (let uu____18119 =
                               let uu____18120 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____18121 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               FStar_Util.format2 "head mismatch (%s vs %s)"
                                 uu____18120 uu____18121
                                in
                             giveup env1 uu____18119 orig))
                 | (HeadMatch (true ),uu____18122) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18135 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____18135 with
                        | (guard,wl2) ->
                            let uu____18142 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____18142)
                     else
                       (let uu____18144 =
                          let uu____18145 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____18146 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____18145 uu____18146
                           in
                        giveup env1 uu____18144 orig)
                 | (uu____18147,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___376_18161 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___376_18161.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___376_18161.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___376_18161.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___376_18161.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___376_18161.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___376_18161.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___376_18161.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___376_18161.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18185 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18185
          then
            let uu____18186 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18186
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18191 =
                let uu____18194 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18194  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18191 t1);
             (let uu____18212 =
                let uu____18215 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18215  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18212 t2);
             (let uu____18233 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18233
              then
                let uu____18234 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18235 =
                  let uu____18236 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18237 =
                    let uu____18238 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18238  in
                  Prims.strcat uu____18236 uu____18237  in
                let uu____18239 =
                  let uu____18240 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18241 =
                    let uu____18242 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18242  in
                  Prims.strcat uu____18240 uu____18241  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18234
                  uu____18235 uu____18239
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18245,uu____18246) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18269,FStar_Syntax_Syntax.Tm_delayed uu____18270) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18293,uu____18294) ->
                  let uu____18321 =
                    let uu___377_18322 = problem  in
                    let uu____18323 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___377_18322.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18323;
                      FStar_TypeChecker_Common.relation =
                        (uu___377_18322.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___377_18322.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___377_18322.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___377_18322.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___377_18322.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___377_18322.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___377_18322.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___377_18322.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18321 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18324,uu____18325) ->
                  let uu____18332 =
                    let uu___378_18333 = problem  in
                    let uu____18334 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___378_18333.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18334;
                      FStar_TypeChecker_Common.relation =
                        (uu___378_18333.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___378_18333.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___378_18333.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___378_18333.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___378_18333.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___378_18333.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___378_18333.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___378_18333.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18332 wl
              | (uu____18335,FStar_Syntax_Syntax.Tm_ascribed uu____18336) ->
                  let uu____18363 =
                    let uu___379_18364 = problem  in
                    let uu____18365 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___379_18364.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___379_18364.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___379_18364.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18365;
                      FStar_TypeChecker_Common.element =
                        (uu___379_18364.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___379_18364.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___379_18364.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___379_18364.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___379_18364.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___379_18364.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18363 wl
              | (uu____18366,FStar_Syntax_Syntax.Tm_meta uu____18367) ->
                  let uu____18374 =
                    let uu___380_18375 = problem  in
                    let uu____18376 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___380_18375.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___380_18375.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___380_18375.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18376;
                      FStar_TypeChecker_Common.element =
                        (uu___380_18375.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___380_18375.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___380_18375.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___380_18375.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___380_18375.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___380_18375.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18374 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18378),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18380)) ->
                  let uu____18389 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18389
              | (FStar_Syntax_Syntax.Tm_bvar uu____18390,uu____18391) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18392,FStar_Syntax_Syntax.Tm_bvar uu____18393) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___335_18462 =
                    match uu___335_18462 with
                    | [] -> c
                    | bs ->
                        let uu____18490 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18490
                     in
                  let uu____18501 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18501 with
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
                                    let uu____18650 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18650
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
                  let mk_t t l uu___336_18735 =
                    match uu___336_18735 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18777 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18777 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____18922 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____18923 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____18922
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____18923 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____18924,uu____18925) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18954 -> true
                    | uu____18973 -> false  in
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
                      (let uu____19026 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___381_19034 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___381_19034.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___381_19034.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___381_19034.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___381_19034.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___381_19034.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___381_19034.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___381_19034.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___381_19034.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___381_19034.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___381_19034.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___381_19034.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___381_19034.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___381_19034.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___381_19034.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___381_19034.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___381_19034.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___381_19034.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___381_19034.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___381_19034.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___381_19034.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___381_19034.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___381_19034.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___381_19034.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___381_19034.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___381_19034.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___381_19034.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___381_19034.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___381_19034.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___381_19034.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___381_19034.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___381_19034.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___381_19034.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___381_19034.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___381_19034.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___381_19034.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___381_19034.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___381_19034.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___381_19034.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___381_19034.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19026 with
                       | (uu____19037,ty,uu____19039) ->
                           let uu____19040 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19040)
                     in
                  let uu____19041 =
                    let uu____19058 = maybe_eta t1  in
                    let uu____19065 = maybe_eta t2  in
                    (uu____19058, uu____19065)  in
                  (match uu____19041 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___382_19107 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___382_19107.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___382_19107.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___382_19107.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___382_19107.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___382_19107.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___382_19107.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___382_19107.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___382_19107.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19128 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19128
                       then
                         let uu____19129 = destruct_flex_t not_abs wl  in
                         (match uu____19129 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___383_19144 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___383_19144.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___383_19144.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___383_19144.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___383_19144.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___383_19144.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___383_19144.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___383_19144.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___383_19144.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19166 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19166
                       then
                         let uu____19167 = destruct_flex_t not_abs wl  in
                         (match uu____19167 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___383_19182 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___383_19182.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___383_19182.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___383_19182.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___383_19182.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___383_19182.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___383_19182.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___383_19182.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___383_19182.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19184 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19201,FStar_Syntax_Syntax.Tm_abs uu____19202) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19231 -> true
                    | uu____19250 -> false  in
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
                      (let uu____19303 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___381_19311 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___381_19311.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___381_19311.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___381_19311.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___381_19311.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___381_19311.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___381_19311.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___381_19311.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___381_19311.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___381_19311.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___381_19311.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___381_19311.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___381_19311.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___381_19311.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___381_19311.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___381_19311.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___381_19311.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___381_19311.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___381_19311.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___381_19311.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___381_19311.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___381_19311.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___381_19311.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___381_19311.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___381_19311.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___381_19311.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___381_19311.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___381_19311.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___381_19311.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___381_19311.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___381_19311.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___381_19311.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___381_19311.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___381_19311.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___381_19311.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___381_19311.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___381_19311.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___381_19311.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___381_19311.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___381_19311.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19303 with
                       | (uu____19314,ty,uu____19316) ->
                           let uu____19317 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19317)
                     in
                  let uu____19318 =
                    let uu____19335 = maybe_eta t1  in
                    let uu____19342 = maybe_eta t2  in
                    (uu____19335, uu____19342)  in
                  (match uu____19318 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___382_19384 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___382_19384.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___382_19384.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___382_19384.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___382_19384.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___382_19384.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___382_19384.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___382_19384.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___382_19384.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19405 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19405
                       then
                         let uu____19406 = destruct_flex_t not_abs wl  in
                         (match uu____19406 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___383_19421 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___383_19421.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___383_19421.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___383_19421.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___383_19421.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___383_19421.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___383_19421.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___383_19421.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___383_19421.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19443 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19443
                       then
                         let uu____19444 = destruct_flex_t not_abs wl  in
                         (match uu____19444 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___383_19459 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___383_19459.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___383_19459.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___383_19459.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___383_19459.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___383_19459.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___383_19459.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___383_19459.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___383_19459.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19461 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19490 =
                    let uu____19495 =
                      head_matches_delta env x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19495 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___384_19523 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___384_19523.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___384_19523.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___385_19525 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___385_19525.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___385_19525.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19526,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___384_19540 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___384_19540.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___384_19540.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___385_19542 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___385_19542.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___385_19542.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19543 -> (x1, x2)  in
                  (match uu____19490 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19562 = as_refinement false env t11  in
                       (match uu____19562 with
                        | (x12,phi11) ->
                            let uu____19569 = as_refinement false env t21  in
                            (match uu____19569 with
                             | (x22,phi21) ->
                                 ((let uu____19577 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19577
                                   then
                                     ((let uu____19579 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19580 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19581 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19579
                                         uu____19580 uu____19581);
                                      (let uu____19582 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19583 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19584 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19582
                                         uu____19583 uu____19584))
                                   else ());
                                  (let uu____19586 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19586 with
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
                                         let uu____19654 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19654
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19666 =
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
                                         (let uu____19677 =
                                            let uu____19680 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19680
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19677
                                            (p_guard base_prob));
                                         (let uu____19698 =
                                            let uu____19701 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19701
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19698
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19719 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19719)
                                          in
                                       let has_uvars =
                                         (let uu____19723 =
                                            let uu____19724 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19724
                                             in
                                          Prims.op_Negation uu____19723) ||
                                           (let uu____19728 =
                                              let uu____19729 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19729
                                               in
                                            Prims.op_Negation uu____19728)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19732 =
                                           let uu____19737 =
                                             let uu____19746 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19746]  in
                                           mk_t_problem wl1 uu____19737 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19732 with
                                          | (ref_prob,wl2) ->
                                              let uu____19767 =
                                                solve env1
                                                  (let uu___386_19769 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___386_19769.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___386_19769.smt_ok);
                                                     tcenv =
                                                       (uu___386_19769.tcenv);
                                                     wl_implicits =
                                                       (uu___386_19769.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19767 with
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
                                               | Success uu____19779 ->
                                                   let guard =
                                                     let uu____19787 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19787
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___387_19796 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___387_19796.attempting);
                                                       wl_deferred =
                                                         (uu___387_19796.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___387_19796.defer_ok);
                                                       smt_ok =
                                                         (uu___387_19796.smt_ok);
                                                       tcenv =
                                                         (uu___387_19796.tcenv);
                                                       wl_implicits =
                                                         (uu___387_19796.wl_implicits)
                                                     }  in
                                                   let uu____19797 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19797))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19799,FStar_Syntax_Syntax.Tm_uvar uu____19800) ->
                  let uu____19825 = destruct_flex_t t1 wl  in
                  (match uu____19825 with
                   | (f1,wl1) ->
                       let uu____19832 = destruct_flex_t t2 wl1  in
                       (match uu____19832 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19839;
                    FStar_Syntax_Syntax.pos = uu____19840;
                    FStar_Syntax_Syntax.vars = uu____19841;_},uu____19842),FStar_Syntax_Syntax.Tm_uvar
                 uu____19843) ->
                  let uu____19892 = destruct_flex_t t1 wl  in
                  (match uu____19892 with
                   | (f1,wl1) ->
                       let uu____19899 = destruct_flex_t t2 wl1  in
                       (match uu____19899 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19906,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19907;
                    FStar_Syntax_Syntax.pos = uu____19908;
                    FStar_Syntax_Syntax.vars = uu____19909;_},uu____19910))
                  ->
                  let uu____19959 = destruct_flex_t t1 wl  in
                  (match uu____19959 with
                   | (f1,wl1) ->
                       let uu____19966 = destruct_flex_t t2 wl1  in
                       (match uu____19966 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19973;
                    FStar_Syntax_Syntax.pos = uu____19974;
                    FStar_Syntax_Syntax.vars = uu____19975;_},uu____19976),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19977;
                    FStar_Syntax_Syntax.pos = uu____19978;
                    FStar_Syntax_Syntax.vars = uu____19979;_},uu____19980))
                  ->
                  let uu____20053 = destruct_flex_t t1 wl  in
                  (match uu____20053 with
                   | (f1,wl1) ->
                       let uu____20060 = destruct_flex_t t2 wl1  in
                       (match uu____20060 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20067,uu____20068) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20081 = destruct_flex_t t1 wl  in
                  (match uu____20081 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20088;
                    FStar_Syntax_Syntax.pos = uu____20089;
                    FStar_Syntax_Syntax.vars = uu____20090;_},uu____20091),uu____20092)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20129 = destruct_flex_t t1 wl  in
                  (match uu____20129 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____20136,FStar_Syntax_Syntax.Tm_uvar uu____20137) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____20150,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20151;
                    FStar_Syntax_Syntax.pos = uu____20152;
                    FStar_Syntax_Syntax.vars = uu____20153;_},uu____20154))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20191,FStar_Syntax_Syntax.Tm_arrow uu____20192) ->
                  solve_t' env
                    (let uu___388_20220 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___388_20220.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___388_20220.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___388_20220.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___388_20220.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___388_20220.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___388_20220.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___388_20220.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___388_20220.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___388_20220.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20221;
                    FStar_Syntax_Syntax.pos = uu____20222;
                    FStar_Syntax_Syntax.vars = uu____20223;_},uu____20224),FStar_Syntax_Syntax.Tm_arrow
                 uu____20225) ->
                  solve_t' env
                    (let uu___388_20277 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___388_20277.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___388_20277.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___388_20277.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___388_20277.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___388_20277.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___388_20277.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___388_20277.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___388_20277.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___388_20277.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20278,FStar_Syntax_Syntax.Tm_uvar uu____20279) ->
                  let uu____20292 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20292
              | (uu____20293,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20294;
                    FStar_Syntax_Syntax.pos = uu____20295;
                    FStar_Syntax_Syntax.vars = uu____20296;_},uu____20297))
                  ->
                  let uu____20334 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20334
              | (FStar_Syntax_Syntax.Tm_uvar uu____20335,uu____20336) ->
                  let uu____20349 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20349
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20350;
                    FStar_Syntax_Syntax.pos = uu____20351;
                    FStar_Syntax_Syntax.vars = uu____20352;_},uu____20353),uu____20354)
                  ->
                  let uu____20391 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20391
              | (FStar_Syntax_Syntax.Tm_refine uu____20392,uu____20393) ->
                  let t21 =
                    let uu____20401 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20401  in
                  solve_t env
                    (let uu___389_20427 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___389_20427.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___389_20427.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___389_20427.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___389_20427.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___389_20427.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___389_20427.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___389_20427.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___389_20427.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___389_20427.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20428,FStar_Syntax_Syntax.Tm_refine uu____20429) ->
                  let t11 =
                    let uu____20437 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20437  in
                  solve_t env
                    (let uu___390_20463 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___390_20463.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___390_20463.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___390_20463.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___390_20463.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___390_20463.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___390_20463.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___390_20463.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___390_20463.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___390_20463.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20545 =
                    let uu____20546 = guard_of_prob env wl problem t1 t2  in
                    match uu____20546 with
                    | (guard,wl1) ->
                        let uu____20553 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20553
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20764 = br1  in
                        (match uu____20764 with
                         | (p1,w1,uu____20789) ->
                             let uu____20806 = br2  in
                             (match uu____20806 with
                              | (p2,w2,uu____20825) ->
                                  let uu____20830 =
                                    let uu____20831 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20831  in
                                  if uu____20830
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20847 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20847 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____20880 = br2  in
                                         (match uu____20880 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____20917 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____20917
                                                 in
                                              let uu____20930 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____20953,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____20970) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____21013 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____21013 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____20930
                                                (fun uu____21055  ->
                                                   match uu____21055 with
                                                   | (wprobs,wl2) ->
                                                       let uu____21076 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____21076
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____21091 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____21091
                                                              (fun
                                                                 uu____21115 
                                                                 ->
                                                                 match uu____21115
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____21200 -> FStar_Pervasives_Native.None  in
                  let uu____21237 = solve_branches wl brs1 brs2  in
                  (match uu____21237 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21265 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21265 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____21284 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21284  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21293 =
                              let uu____21294 =
                                attempt sub_probs1
                                  (let uu___391_21296 = wl3  in
                                   {
                                     attempting = (uu___391_21296.attempting);
                                     wl_deferred =
                                       (uu___391_21296.wl_deferred);
                                     ctr = (uu___391_21296.ctr);
                                     defer_ok = (uu___391_21296.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___391_21296.tcenv);
                                     wl_implicits =
                                       (uu___391_21296.wl_implicits)
                                   })
                                 in
                              solve env uu____21294  in
                            (match uu____21293 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21300 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21306,uu____21307) ->
                  let head1 =
                    let uu____21331 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21331
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21377 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21377
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21423 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21423
                    then
                      let uu____21424 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21425 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21426 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21424 uu____21425 uu____21426
                    else ());
                   (let no_free_uvars t =
                      (let uu____21436 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21436) &&
                        (let uu____21440 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21440)
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
                      let uu____21456 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21456 = FStar_Syntax_Util.Equal  in
                    let uu____21457 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21457
                    then
                      let uu____21458 =
                        let uu____21465 = equal t1 t2  in
                        if uu____21465
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21475 = mk_eq2 wl orig t1 t2  in
                           match uu____21475 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21458 with
                      | (guard,wl1) ->
                          let uu____21496 = solve_prob orig guard [] wl1  in
                          solve env uu____21496
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21498,uu____21499) ->
                  let head1 =
                    let uu____21507 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21507
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21553 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21553
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21599 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21599
                    then
                      let uu____21600 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21601 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21602 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21600 uu____21601 uu____21602
                    else ());
                   (let no_free_uvars t =
                      (let uu____21612 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21612) &&
                        (let uu____21616 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21616)
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
                      let uu____21632 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21632 = FStar_Syntax_Util.Equal  in
                    let uu____21633 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21633
                    then
                      let uu____21634 =
                        let uu____21641 = equal t1 t2  in
                        if uu____21641
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21651 = mk_eq2 wl orig t1 t2  in
                           match uu____21651 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21634 with
                      | (guard,wl1) ->
                          let uu____21672 = solve_prob orig guard [] wl1  in
                          solve env uu____21672
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____21674,uu____21675) ->
                  let head1 =
                    let uu____21677 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21677
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21723 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21723
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21769 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21769
                    then
                      let uu____21770 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21771 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21772 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21770 uu____21771 uu____21772
                    else ());
                   (let no_free_uvars t =
                      (let uu____21782 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21782) &&
                        (let uu____21786 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21786)
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
                      let uu____21802 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21802 = FStar_Syntax_Util.Equal  in
                    let uu____21803 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21803
                    then
                      let uu____21804 =
                        let uu____21811 = equal t1 t2  in
                        if uu____21811
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21821 = mk_eq2 wl orig t1 t2  in
                           match uu____21821 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21804 with
                      | (guard,wl1) ->
                          let uu____21842 = solve_prob orig guard [] wl1  in
                          solve env uu____21842
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____21844,uu____21845) ->
                  let head1 =
                    let uu____21847 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21847
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21893 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21893
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21939 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21939
                    then
                      let uu____21940 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21941 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21942 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21940 uu____21941 uu____21942
                    else ());
                   (let no_free_uvars t =
                      (let uu____21952 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21952) &&
                        (let uu____21956 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21956)
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
                      let uu____21972 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21972 = FStar_Syntax_Util.Equal  in
                    let uu____21973 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21973
                    then
                      let uu____21974 =
                        let uu____21981 = equal t1 t2  in
                        if uu____21981
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21991 = mk_eq2 wl orig t1 t2  in
                           match uu____21991 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21974 with
                      | (guard,wl1) ->
                          let uu____22012 = solve_prob orig guard [] wl1  in
                          solve env uu____22012
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____22014,uu____22015) ->
                  let head1 =
                    let uu____22017 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22017
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22063 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22063
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22109 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22109
                    then
                      let uu____22110 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22111 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22112 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22110 uu____22111 uu____22112
                    else ());
                   (let no_free_uvars t =
                      (let uu____22122 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22122) &&
                        (let uu____22126 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22126)
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
                      let uu____22142 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22142 = FStar_Syntax_Util.Equal  in
                    let uu____22143 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22143
                    then
                      let uu____22144 =
                        let uu____22151 = equal t1 t2  in
                        if uu____22151
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22161 = mk_eq2 wl orig t1 t2  in
                           match uu____22161 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22144 with
                      | (guard,wl1) ->
                          let uu____22182 = solve_prob orig guard [] wl1  in
                          solve env uu____22182
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22184,uu____22185) ->
                  let head1 =
                    let uu____22203 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22203
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22249 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22249
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22295 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22295
                    then
                      let uu____22296 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22297 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22298 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22296 uu____22297 uu____22298
                    else ());
                   (let no_free_uvars t =
                      (let uu____22308 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22308) &&
                        (let uu____22312 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22312)
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
                      let uu____22328 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22328 = FStar_Syntax_Util.Equal  in
                    let uu____22329 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22329
                    then
                      let uu____22330 =
                        let uu____22337 = equal t1 t2  in
                        if uu____22337
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22347 = mk_eq2 wl orig t1 t2  in
                           match uu____22347 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22330 with
                      | (guard,wl1) ->
                          let uu____22368 = solve_prob orig guard [] wl1  in
                          solve env uu____22368
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22370,FStar_Syntax_Syntax.Tm_match uu____22371) ->
                  let head1 =
                    let uu____22395 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22395
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22441 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22441
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22487 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22487
                    then
                      let uu____22488 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22489 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22490 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22488 uu____22489 uu____22490
                    else ());
                   (let no_free_uvars t =
                      (let uu____22500 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22500) &&
                        (let uu____22504 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22504)
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
                      let uu____22520 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22520 = FStar_Syntax_Util.Equal  in
                    let uu____22521 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22521
                    then
                      let uu____22522 =
                        let uu____22529 = equal t1 t2  in
                        if uu____22529
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22539 = mk_eq2 wl orig t1 t2  in
                           match uu____22539 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22522 with
                      | (guard,wl1) ->
                          let uu____22560 = solve_prob orig guard [] wl1  in
                          solve env uu____22560
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22562,FStar_Syntax_Syntax.Tm_uinst uu____22563) ->
                  let head1 =
                    let uu____22571 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22571
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22611 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22611
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22651 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22651
                    then
                      let uu____22652 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22653 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22654 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22652 uu____22653 uu____22654
                    else ());
                   (let no_free_uvars t =
                      (let uu____22664 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22664) &&
                        (let uu____22668 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22668)
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
                      let uu____22684 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22684 = FStar_Syntax_Util.Equal  in
                    let uu____22685 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22685
                    then
                      let uu____22686 =
                        let uu____22693 = equal t1 t2  in
                        if uu____22693
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22703 = mk_eq2 wl orig t1 t2  in
                           match uu____22703 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22686 with
                      | (guard,wl1) ->
                          let uu____22724 = solve_prob orig guard [] wl1  in
                          solve env uu____22724
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22726,FStar_Syntax_Syntax.Tm_name uu____22727) ->
                  let head1 =
                    let uu____22729 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22729
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22769 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22769
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22809 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22809
                    then
                      let uu____22810 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22811 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22812 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22810 uu____22811 uu____22812
                    else ());
                   (let no_free_uvars t =
                      (let uu____22822 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22822) &&
                        (let uu____22826 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22826)
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
                      let uu____22842 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22842 = FStar_Syntax_Util.Equal  in
                    let uu____22843 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22843
                    then
                      let uu____22844 =
                        let uu____22851 = equal t1 t2  in
                        if uu____22851
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22861 = mk_eq2 wl orig t1 t2  in
                           match uu____22861 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22844 with
                      | (guard,wl1) ->
                          let uu____22882 = solve_prob orig guard [] wl1  in
                          solve env uu____22882
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22884,FStar_Syntax_Syntax.Tm_constant uu____22885) ->
                  let head1 =
                    let uu____22887 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22887
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22927 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22927
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22967 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22967
                    then
                      let uu____22968 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22969 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22970 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22968 uu____22969 uu____22970
                    else ());
                   (let no_free_uvars t =
                      (let uu____22980 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22980) &&
                        (let uu____22984 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22984)
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
                      let uu____23000 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23000 = FStar_Syntax_Util.Equal  in
                    let uu____23001 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23001
                    then
                      let uu____23002 =
                        let uu____23009 = equal t1 t2  in
                        if uu____23009
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23019 = mk_eq2 wl orig t1 t2  in
                           match uu____23019 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23002 with
                      | (guard,wl1) ->
                          let uu____23040 = solve_prob orig guard [] wl1  in
                          solve env uu____23040
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23042,FStar_Syntax_Syntax.Tm_fvar uu____23043) ->
                  let head1 =
                    let uu____23045 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23045
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23091 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23091
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23137 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23137
                    then
                      let uu____23138 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23139 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23140 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23138 uu____23139 uu____23140
                    else ());
                   (let no_free_uvars t =
                      (let uu____23150 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23150) &&
                        (let uu____23154 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23154)
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
                      let uu____23170 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23170 = FStar_Syntax_Util.Equal  in
                    let uu____23171 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23171
                    then
                      let uu____23172 =
                        let uu____23179 = equal t1 t2  in
                        if uu____23179
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23189 = mk_eq2 wl orig t1 t2  in
                           match uu____23189 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23172 with
                      | (guard,wl1) ->
                          let uu____23210 = solve_prob orig guard [] wl1  in
                          solve env uu____23210
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23212,FStar_Syntax_Syntax.Tm_app uu____23213) ->
                  let head1 =
                    let uu____23231 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23231
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23271 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23271
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23311 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23311
                    then
                      let uu____23312 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23313 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23314 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23312 uu____23313 uu____23314
                    else ());
                   (let no_free_uvars t =
                      (let uu____23324 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23324) &&
                        (let uu____23328 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23328)
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
                      let uu____23344 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23344 = FStar_Syntax_Util.Equal  in
                    let uu____23345 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23345
                    then
                      let uu____23346 =
                        let uu____23353 = equal t1 t2  in
                        if uu____23353
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23363 = mk_eq2 wl orig t1 t2  in
                           match uu____23363 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23346 with
                      | (guard,wl1) ->
                          let uu____23384 = solve_prob orig guard [] wl1  in
                          solve env uu____23384
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23386,FStar_Syntax_Syntax.Tm_let uu____23387) ->
                  let uu____23412 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23412
                  then
                    let uu____23413 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23413
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23415,uu____23416) ->
                  let uu____23429 =
                    let uu____23434 =
                      let uu____23435 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23436 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23437 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23438 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23435 uu____23436 uu____23437 uu____23438
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23434)
                     in
                  FStar_Errors.raise_error uu____23429
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23439,FStar_Syntax_Syntax.Tm_let uu____23440) ->
                  let uu____23453 =
                    let uu____23458 =
                      let uu____23459 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23460 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23461 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23462 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23459 uu____23460 uu____23461 uu____23462
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23458)
                     in
                  FStar_Errors.raise_error uu____23453
                    t1.FStar_Syntax_Syntax.pos
              | uu____23463 -> giveup env "head tag mismatch" orig))))

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
          (let uu____23524 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23524
           then
             let uu____23525 =
               let uu____23526 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23526  in
             let uu____23527 =
               let uu____23528 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23528  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23525 uu____23527
           else ());
          (let uu____23530 =
             let uu____23531 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23531  in
           if uu____23530
           then
             let uu____23532 =
               let uu____23533 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23534 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23533 uu____23534
                in
             giveup env uu____23532 orig
           else
             (let uu____23536 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23536 with
              | (ret_sub_prob,wl1) ->
                  let uu____23543 =
                    FStar_List.fold_right2
                      (fun uu____23580  ->
                         fun uu____23581  ->
                           fun uu____23582  ->
                             match (uu____23580, uu____23581, uu____23582)
                             with
                             | ((a1,uu____23626),(a2,uu____23628),(arg_sub_probs,wl2))
                                 ->
                                 let uu____23661 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____23661 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23543 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____23690 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____23690  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____23698 = attempt sub_probs wl3  in
                       solve env uu____23698)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23721 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23724)::[] -> wp1
              | uu____23749 ->
                  let uu____23760 =
                    let uu____23761 =
                      let uu____23762 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23762  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23761
                     in
                  failwith uu____23760
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23768 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23768]
              | x -> x  in
            let uu____23770 =
              let uu____23781 =
                let uu____23790 =
                  let uu____23791 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23791 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23790  in
              [uu____23781]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23770;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23808 = lift_c1 ()  in solve_eq uu____23808 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___337_23814  ->
                       match uu___337_23814 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23815 -> false))
                in
             let uu____23816 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23846)::uu____23847,(wp2,uu____23849)::uu____23850)
                   -> (wp1, wp2)
               | uu____23923 ->
                   let uu____23948 =
                     let uu____23953 =
                       let uu____23954 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23955 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23954 uu____23955
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23953)
                      in
                   FStar_Errors.raise_error uu____23948
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23816 with
             | (wpc1,wpc2) ->
                 let uu____23962 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23962
                 then
                   let uu____23965 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23965 wl
                 else
                   (let uu____23967 =
                      let uu____23974 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23974  in
                    match uu____23967 with
                    | (c2_decl,qualifiers) ->
                        let uu____23995 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____23995
                        then
                          let c1_repr =
                            let uu____23999 =
                              let uu____24000 =
                                let uu____24001 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____24001  in
                              let uu____24002 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24000 uu____24002
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____23999
                             in
                          let c2_repr =
                            let uu____24004 =
                              let uu____24005 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____24006 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24005 uu____24006
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24004
                             in
                          let uu____24007 =
                            let uu____24012 =
                              let uu____24013 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____24014 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____24013 uu____24014
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____24012
                             in
                          (match uu____24007 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____24018 = attempt [prob] wl2  in
                               solve env uu____24018)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____24029 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24029
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____24032 =
                                     let uu____24039 =
                                       let uu____24040 =
                                         let uu____24057 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____24060 =
                                           let uu____24071 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____24080 =
                                             let uu____24091 =
                                               let uu____24100 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____24100
                                                in
                                             [uu____24091]  in
                                           uu____24071 :: uu____24080  in
                                         (uu____24057, uu____24060)  in
                                       FStar_Syntax_Syntax.Tm_app uu____24040
                                        in
                                     FStar_Syntax_Syntax.mk uu____24039  in
                                   uu____24032 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____24151 =
                                    let uu____24158 =
                                      let uu____24159 =
                                        let uu____24176 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____24179 =
                                          let uu____24190 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24199 =
                                            let uu____24210 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24219 =
                                              let uu____24230 =
                                                let uu____24239 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24239
                                                 in
                                              [uu____24230]  in
                                            uu____24210 :: uu____24219  in
                                          uu____24190 :: uu____24199  in
                                        (uu____24176, uu____24179)  in
                                      FStar_Syntax_Syntax.Tm_app uu____24159
                                       in
                                    FStar_Syntax_Syntax.mk uu____24158  in
                                  uu____24151 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24296 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24296
                            then
                              let uu____24297 =
                                let uu____24298 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24298
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24297
                            else ());
                           (let uu____24300 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24300 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24308 =
                                    let uu____24311 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24311
                                     in
                                  solve_prob orig uu____24308 [] wl1  in
                                let uu____24314 = attempt [base_prob] wl2  in
                                solve env uu____24314))))
           in
        let uu____24315 = FStar_Util.physical_equality c1 c2  in
        if uu____24315
        then
          let uu____24316 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24316
        else
          ((let uu____24319 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24319
            then
              let uu____24320 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24321 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24320
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24321
            else ());
           (let uu____24323 =
              let uu____24332 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24335 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24332, uu____24335)  in
            match uu____24323 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24353),FStar_Syntax_Syntax.Total
                    (t2,uu____24355)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24372 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24372 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24373,FStar_Syntax_Syntax.Total uu____24374) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24392),FStar_Syntax_Syntax.Total
                    (t2,uu____24394)) ->
                     let uu____24411 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24411 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24413),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24415)) ->
                     let uu____24432 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24432 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24434),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24436)) ->
                     let uu____24453 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24453 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24454,FStar_Syntax_Syntax.Comp uu____24455) ->
                     let uu____24464 =
                       let uu___392_24467 = problem  in
                       let uu____24470 =
                         let uu____24471 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24471
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___392_24467.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24470;
                         FStar_TypeChecker_Common.relation =
                           (uu___392_24467.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___392_24467.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___392_24467.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___392_24467.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___392_24467.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___392_24467.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___392_24467.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___392_24467.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24464 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24472,FStar_Syntax_Syntax.Comp uu____24473) ->
                     let uu____24482 =
                       let uu___392_24485 = problem  in
                       let uu____24488 =
                         let uu____24489 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24489
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___392_24485.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24488;
                         FStar_TypeChecker_Common.relation =
                           (uu___392_24485.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___392_24485.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___392_24485.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___392_24485.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___392_24485.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___392_24485.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___392_24485.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___392_24485.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24482 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24490,FStar_Syntax_Syntax.GTotal uu____24491) ->
                     let uu____24500 =
                       let uu___393_24503 = problem  in
                       let uu____24506 =
                         let uu____24507 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24507
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___393_24503.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___393_24503.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___393_24503.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24506;
                         FStar_TypeChecker_Common.element =
                           (uu___393_24503.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___393_24503.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___393_24503.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___393_24503.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___393_24503.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___393_24503.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24500 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24508,FStar_Syntax_Syntax.Total uu____24509) ->
                     let uu____24518 =
                       let uu___393_24521 = problem  in
                       let uu____24524 =
                         let uu____24525 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24525
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___393_24521.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___393_24521.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___393_24521.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24524;
                         FStar_TypeChecker_Common.element =
                           (uu___393_24521.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___393_24521.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___393_24521.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___393_24521.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___393_24521.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___393_24521.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24518 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24526,FStar_Syntax_Syntax.Comp uu____24527) ->
                     let uu____24528 =
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
                     if uu____24528
                     then
                       let uu____24529 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24529 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24533 =
                            let uu____24538 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24538
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24544 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24545 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24544, uu____24545))
                             in
                          match uu____24533 with
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
                           (let uu____24552 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24552
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24554 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24554 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24557 =
                                  let uu____24558 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24559 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24558 uu____24559
                                   in
                                giveup env uu____24557 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24566 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24566 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24607 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24607 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24625 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24653  ->
                match uu____24653 with
                | (u1,u2) ->
                    let uu____24660 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24661 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24660 uu____24661))
         in
      FStar_All.pipe_right uu____24625 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24688,[])) -> "{}"
      | uu____24713 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24736 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____24736
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24739 =
              FStar_List.map
                (fun uu____24749  ->
                   match uu____24749 with
                   | (uu____24754,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24739 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24759 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24759 imps
  
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
                  let uu____24812 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____24812
                  then
                    let uu____24813 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____24814 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24813
                      (rel_to_string rel) uu____24814
                  else "TOP"  in
                let uu____24816 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____24816 with
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
              let uu____24874 =
                let uu____24877 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____24877
                 in
              FStar_Syntax_Syntax.new_bv uu____24874 t1  in
            let uu____24880 =
              let uu____24885 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____24885
               in
            match uu____24880 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____24958 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____24958
              then
                let uu____24959 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____24959
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
          ((let uu____24981 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____24981
            then
              let uu____24982 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____24982
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____24986 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____24986
             then
               let uu____24987 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____24987
             else ());
            (let f2 =
               let uu____24990 =
                 let uu____24991 = FStar_Syntax_Util.unmeta f1  in
                 uu____24991.FStar_Syntax_Syntax.n  in
               match uu____24990 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____24995 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___394_24996 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___394_24996.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___394_24996.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___394_24996.FStar_TypeChecker_Env.implicits)
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
            let uu____25050 =
              let uu____25051 =
                let uu____25052 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____25052;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____25051  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____25050
  
let with_guard_no_simp :
  'Auu____25067 .
    'Auu____25067 ->
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
            let uu____25090 =
              let uu____25091 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____25091;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____25090
  
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
          (let uu____25121 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____25121
           then
             let uu____25122 = FStar_Syntax_Print.term_to_string t1  in
             let uu____25123 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____25122
               uu____25123
           else ());
          (let uu____25125 =
             let uu____25130 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____25130
              in
           match uu____25125 with
           | (prob,wl) ->
               let g =
                 let uu____25138 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____25148  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____25138  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25182 = try_teq true env t1 t2  in
        match uu____25182 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25186 = FStar_TypeChecker_Env.get_range env  in
              let uu____25187 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25186 uu____25187);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25194 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25194
              then
                let uu____25195 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25196 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25197 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25195
                  uu____25196 uu____25197
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
          let uu____25219 = FStar_TypeChecker_Env.get_range env  in
          let uu____25220 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25219 uu____25220
  
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
        (let uu____25245 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25245
         then
           let uu____25246 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25247 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25246 uu____25247
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25250 =
           let uu____25257 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25257 "sub_comp"
            in
         match uu____25250 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25268 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25278  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25268)))
  
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
      fun uu____25323  ->
        match uu____25323 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25366 =
                 let uu____25371 =
                   let uu____25372 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25373 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25372 uu____25373
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25371)  in
               let uu____25374 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25366 uu____25374)
               in
            let equiv1 v1 v' =
              let uu____25386 =
                let uu____25391 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25392 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25391, uu____25392)  in
              match uu____25386 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25411 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25441 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25441 with
                      | FStar_Syntax_Syntax.U_unif uu____25448 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25477  ->
                                    match uu____25477 with
                                    | (u,v') ->
                                        let uu____25486 = equiv1 v1 v'  in
                                        if uu____25486
                                        then
                                          let uu____25489 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25489 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25505 -> []))
               in
            let uu____25510 =
              let wl =
                let uu___395_25514 = empty_worklist env  in
                {
                  attempting = (uu___395_25514.attempting);
                  wl_deferred = (uu___395_25514.wl_deferred);
                  ctr = (uu___395_25514.ctr);
                  defer_ok = false;
                  smt_ok = (uu___395_25514.smt_ok);
                  tcenv = (uu___395_25514.tcenv);
                  wl_implicits = (uu___395_25514.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25532  ->
                      match uu____25532 with
                      | (lb,v1) ->
                          let uu____25539 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25539 with
                           | USolved wl1 -> ()
                           | uu____25541 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25551 =
              match uu____25551 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25560) -> true
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
                      uu____25583,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25585,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25596) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25603,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25611 -> false)
               in
            let uu____25616 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25631  ->
                      match uu____25631 with
                      | (u,v1) ->
                          let uu____25638 = check_ineq (u, v1)  in
                          if uu____25638
                          then true
                          else
                            ((let uu____25641 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____25641
                              then
                                let uu____25642 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____25643 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____25642
                                  uu____25643
                              else ());
                             false)))
               in
            if uu____25616
            then ()
            else
              ((let uu____25647 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25647
                then
                  ((let uu____25649 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25649);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25659 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25659))
                else ());
               (let uu____25669 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25669))
  
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
        let fail1 uu____25736 =
          match uu____25736 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___396_25757 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___396_25757.attempting);
            wl_deferred = (uu___396_25757.wl_deferred);
            ctr = (uu___396_25757.ctr);
            defer_ok;
            smt_ok = (uu___396_25757.smt_ok);
            tcenv = (uu___396_25757.tcenv);
            wl_implicits = (uu___396_25757.wl_implicits)
          }  in
        (let uu____25759 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25759
         then
           let uu____25760 = FStar_Util.string_of_bool defer_ok  in
           let uu____25761 = wl_to_string wl  in
           let uu____25762 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____25760 uu____25761 uu____25762
         else ());
        (let g1 =
           let uu____25765 = solve_and_commit env wl fail1  in
           match uu____25765 with
           | FStar_Pervasives_Native.Some
               (uu____25772::uu____25773,uu____25774) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___397_25799 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___397_25799.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___397_25799.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____25800 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___398_25808 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___398_25808.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___398_25808.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___398_25808.FStar_TypeChecker_Env.implicits)
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
    let uu____25856 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25856 with
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
            let uu___399_25967 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___399_25967.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___399_25967.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___399_25967.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____25968 =
            let uu____25969 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____25969  in
          if uu____25968
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____25977 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____25978 =
                       let uu____25979 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____25979
                        in
                     FStar_Errors.diag uu____25977 uu____25978)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____25983 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____25984 =
                        let uu____25985 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____25985
                         in
                      FStar_Errors.diag uu____25983 uu____25984)
                   else ();
                   (let uu____25988 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____25988
                      "discharge_guard'" env vc1);
                   (let uu____25989 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____25989 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____25996 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____25997 =
                                let uu____25998 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____25998
                                 in
                              FStar_Errors.diag uu____25996 uu____25997)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____26003 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26004 =
                                let uu____26005 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____26005
                                 in
                              FStar_Errors.diag uu____26003 uu____26004)
                           else ();
                           (let vcs =
                              let uu____26016 = FStar_Options.use_tactics ()
                                 in
                              if uu____26016
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____26036  ->
                                     (let uu____26038 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a236  -> ())
                                        uu____26038);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____26081  ->
                                              match uu____26081 with
                                              | (env1,goal,opts) ->
                                                  let uu____26097 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____26097, opts)))))
                              else
                                (let uu____26099 =
                                   let uu____26106 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____26106)  in
                                 [uu____26099])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____26139  ->
                                    match uu____26139 with
                                    | (env1,goal,opts) ->
                                        let uu____26149 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____26149 with
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
                                                (let uu____26157 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26158 =
                                                   let uu____26159 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____26160 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____26159 uu____26160
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26157 uu____26158)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____26163 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26164 =
                                                   let uu____26165 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____26165
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26163 uu____26164)
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
      let uu____26179 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26179 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26186 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26186
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26197 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26197 with
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
        let uu____26223 = try_teq false env t1 t2  in
        match uu____26223 with
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
            let uu____26258 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26258 with
            | FStar_Pervasives_Native.Some uu____26261 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26281 = acc  in
            match uu____26281 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26293 = hd1  in
                     (match uu____26293 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26298;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26306 = unresolved ctx_u  in
                             if uu____26306
                             then
                               match hd1.FStar_TypeChecker_Env.imp_meta with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env1,tau) ->
                                   let t =
                                     env1.FStar_TypeChecker_Env.synth_hook
                                       env1
                                       (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                       tau
                                      in
                                   let extra =
                                     let uu____26321 = teq_nosmt env1 t tm
                                        in
                                     match uu____26321 with
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "resolve_implicits: unifying with an unresolved uvar failed?"
                                     | FStar_Pervasives_Native.Some g1 ->
                                         g1.FStar_TypeChecker_Env.implicits
                                      in
                                   let hd2 =
                                     let uu___400_26330 = hd1  in
                                     {
                                       FStar_TypeChecker_Env.imp_reason =
                                         (uu___400_26330.FStar_TypeChecker_Env.imp_reason);
                                       FStar_TypeChecker_Env.imp_uvar =
                                         (uu___400_26330.FStar_TypeChecker_Env.imp_uvar);
                                       FStar_TypeChecker_Env.imp_tm =
                                         (uu___400_26330.FStar_TypeChecker_Env.imp_tm);
                                       FStar_TypeChecker_Env.imp_range =
                                         (uu___400_26330.FStar_TypeChecker_Env.imp_range);
                                       FStar_TypeChecker_Env.imp_meta =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   until_fixpoint (out, changed) (hd2 ::
                                     (FStar_List.append extra tl1))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___401_26338 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___401_26338.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___401_26338.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___401_26338.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___401_26338.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___401_26338.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___401_26338.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___401_26338.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___401_26338.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___401_26338.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___401_26338.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___401_26338.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___401_26338.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___401_26338.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___401_26338.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___401_26338.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___401_26338.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___401_26338.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___401_26338.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___401_26338.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___401_26338.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___401_26338.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___401_26338.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___401_26338.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___401_26338.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___401_26338.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___401_26338.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___401_26338.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___401_26338.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___401_26338.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___401_26338.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___401_26338.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___401_26338.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___401_26338.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___401_26338.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___401_26338.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___401_26338.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___401_26338.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___401_26338.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___401_26338.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___401_26338.FStar_TypeChecker_Env.dep_graph);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___401_26338.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___402_26341 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___402_26341.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___402_26341.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___402_26341.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___402_26341.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___402_26341.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___402_26341.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___402_26341.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___402_26341.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___402_26341.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___402_26341.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___402_26341.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___402_26341.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___402_26341.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___402_26341.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___402_26341.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___402_26341.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___402_26341.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___402_26341.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___402_26341.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___402_26341.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___402_26341.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___402_26341.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___402_26341.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___402_26341.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___402_26341.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___402_26341.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___402_26341.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___402_26341.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___402_26341.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___402_26341.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___402_26341.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___402_26341.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___402_26341.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___402_26341.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___402_26341.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___402_26341.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___402_26341.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___402_26341.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___402_26341.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___402_26341.FStar_TypeChecker_Env.dep_graph);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___402_26341.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26344 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26344
                                   then
                                     let uu____26345 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26346 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26347 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26348 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26345 uu____26346 uu____26347
                                       reason uu____26348
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___404_26352  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26359 =
                                             let uu____26368 =
                                               let uu____26375 =
                                                 let uu____26376 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26377 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26378 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26376 uu____26377
                                                   uu____26378
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26375, r)
                                                in
                                             [uu____26368]  in
                                           FStar_Errors.add_errors
                                             uu____26359);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___405_26392 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___405_26392.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___405_26392.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___405_26392.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26395 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26405  ->
                                               let uu____26406 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26407 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26408 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26406 uu____26407
                                                 reason uu____26408)) env2 g2
                                         true
                                        in
                                     match uu____26395 with
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
          let uu___406_26410 = g  in
          let uu____26411 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___406_26410.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___406_26410.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___406_26410.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26411
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
        let uu____26445 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26445 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26446 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a237  -> ()) uu____26446
      | imp::uu____26448 ->
          let uu____26451 =
            let uu____26456 =
              let uu____26457 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26458 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26457 uu____26458 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26456)
             in
          FStar_Errors.raise_error uu____26451
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26474 = teq_nosmt env t1 t2  in
        match uu____26474 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___407_26489 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___407_26489.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___407_26489.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___407_26489.FStar_TypeChecker_Env.implicits)
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
        (let uu____26524 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26524
         then
           let uu____26525 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26526 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26525
             uu____26526
         else ());
        (let uu____26528 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26528 with
         | (prob,x,wl) ->
             let g =
               let uu____26547 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26557  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26547  in
             ((let uu____26577 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26577
               then
                 let uu____26578 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26579 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26580 =
                   let uu____26581 = FStar_Util.must g  in
                   guard_to_string env uu____26581  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26578 uu____26579 uu____26580
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
        let uu____26615 = check_subtyping env t1 t2  in
        match uu____26615 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26634 =
              let uu____26635 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____26635 g  in
            FStar_Pervasives_Native.Some uu____26634
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26653 = check_subtyping env t1 t2  in
        match uu____26653 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26672 =
              let uu____26673 =
                let uu____26674 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26674]  in
              FStar_TypeChecker_Env.close_guard env uu____26673 g  in
            FStar_Pervasives_Native.Some uu____26672
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26711 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26711
         then
           let uu____26712 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26713 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26712
             uu____26713
         else ());
        (let uu____26715 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26715 with
         | (prob,x,wl) ->
             let g =
               let uu____26730 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____26740  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26730  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26763 =
                      let uu____26764 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26764]  in
                    FStar_TypeChecker_Env.close_guard env uu____26763 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26801 = subtype_nosmt env t1 t2  in
        match uu____26801 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  