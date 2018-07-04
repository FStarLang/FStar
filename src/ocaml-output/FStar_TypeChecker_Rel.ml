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
                   (let uu___344_390 = wl  in
                    {
                      attempting = (uu___344_390.attempting);
                      wl_deferred = (uu___344_390.wl_deferred);
                      ctr = (uu___344_390.ctr);
                      defer_ok = (uu___344_390.defer_ok);
                      smt_ok = (uu___344_390.smt_ok);
                      tcenv = (uu___344_390.tcenv);
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
            let uu___345_422 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___345_422.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___345_422.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___345_422.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___345_422.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___345_422.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___345_422.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___345_422.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___345_422.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___345_422.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___345_422.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___345_422.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___345_422.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___345_422.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___345_422.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___345_422.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___345_422.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___345_422.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___345_422.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___345_422.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___345_422.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___345_422.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___345_422.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___345_422.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___345_422.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___345_422.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___345_422.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___345_422.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___345_422.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___345_422.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___345_422.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___345_422.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___345_422.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___345_422.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___345_422.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___345_422.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___345_422.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___345_422.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___345_422.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___345_422.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___345_422.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___345_422.FStar_TypeChecker_Env.nbe)
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
  fun uu___311_543  ->
    match uu___311_543 with
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
    fun uu___312_638  ->
      match uu___312_638 with
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
    fun uu___313_672  ->
      match uu___313_672 with
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
  fun uu___314_810  ->
    match uu___314_810 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____815 .
    'Auu____815 FStar_TypeChecker_Common.problem ->
      'Auu____815 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___346_827 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___346_827.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___346_827.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___346_827.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___346_827.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___346_827.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___346_827.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___346_827.FStar_TypeChecker_Common.rank)
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
  fun uu___315_851  ->
    match uu___315_851 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___316_866  ->
    match uu___316_866 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___347_872 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___347_872.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___347_872.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___347_872.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___347_872.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___347_872.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___347_872.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___347_872.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___347_872.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___347_872.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___348_880 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___348_880.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___348_880.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___348_880.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___348_880.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___348_880.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___348_880.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___348_880.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___348_880.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___348_880.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___317_892  ->
      match uu___317_892 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___318_897  ->
    match uu___318_897 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___319_908  ->
    match uu___319_908 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___320_921  ->
    match uu___320_921 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___321_934  ->
    match uu___321_934 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___322_947  ->
    match uu___322_947 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___323_960  ->
    match uu___323_960 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___324_971  ->
    match uu___324_971 with
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
        let uu___349_1340 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___349_1340.wl_deferred);
          ctr = (uu___349_1340.ctr);
          defer_ok = (uu___349_1340.defer_ok);
          smt_ok;
          tcenv = (uu___349_1340.tcenv);
          wl_implicits = (uu___349_1340.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1347 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1347,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___350_1370 = empty_worklist env  in
      let uu____1371 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1371;
        wl_deferred = (uu___350_1370.wl_deferred);
        ctr = (uu___350_1370.ctr);
        defer_ok = (uu___350_1370.defer_ok);
        smt_ok = (uu___350_1370.smt_ok);
        tcenv = (uu___350_1370.tcenv);
        wl_implicits = (uu___350_1370.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___351_1391 = wl  in
        {
          attempting = (uu___351_1391.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___351_1391.ctr);
          defer_ok = (uu___351_1391.defer_ok);
          smt_ok = (uu___351_1391.smt_ok);
          tcenv = (uu___351_1391.tcenv);
          wl_implicits = (uu___351_1391.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___352_1413 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___352_1413.wl_deferred);
         ctr = (uu___352_1413.ctr);
         defer_ok = (uu___352_1413.defer_ok);
         smt_ok = (uu___352_1413.smt_ok);
         tcenv = (uu___352_1413.tcenv);
         wl_implicits = (uu___352_1413.wl_implicits)
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
  fun uu___325_1484  ->
    match uu___325_1484 with
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
                      (let uu___353_2074 = wl  in
                       {
                         attempting = (uu___353_2074.attempting);
                         wl_deferred = (uu___353_2074.wl_deferred);
                         ctr = (uu___353_2074.ctr);
                         defer_ok = (uu___353_2074.defer_ok);
                         smt_ok = (uu___353_2074.smt_ok);
                         tcenv = env;
                         wl_implicits = (uu___353_2074.wl_implicits)
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
         (fun uu___326_2295  ->
            match uu___326_2295 with
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
        (fun uu___327_2340  ->
           match uu___327_2340 with
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
        (fun uu___328_2374  ->
           match uu___328_2374 with
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
        let uu____2395 =
          let uu____2396 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2396
           in
        FStar_Syntax_Subst.compress uu____2395  in
      FStar_All.pipe_right uu____2394 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2407 =
        let uu____2408 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t
           in
        FStar_Syntax_Subst.compress uu____2408  in
      FStar_All.pipe_right uu____2407 FStar_Syntax_Util.unlazy_emb
  
let norm_arg :
  'Auu____2415 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2415) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2415)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2438 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2438, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2489  ->
              match uu____2489 with
              | (x,imp) ->
                  let uu____2508 =
                    let uu___354_2509 = x  in
                    let uu____2510 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___354_2509.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___354_2509.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2510
                    }  in
                  (uu____2508, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2533 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2533
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2537 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2537
        | uu____2540 -> u2  in
      let uu____2541 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2541
  
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
                (let uu____2663 = norm_refinement env t12  in
                 match uu____2663 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2680;
                     FStar_Syntax_Syntax.vars = uu____2681;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2707 =
                       let uu____2708 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2709 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2708 uu____2709
                        in
                     failwith uu____2707)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2725 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2725
          | FStar_Syntax_Syntax.Tm_uinst uu____2726 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2765 =
                   let uu____2766 = FStar_Syntax_Subst.compress t1'  in
                   uu____2766.FStar_Syntax_Syntax.n  in
                 match uu____2765 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2783 -> aux true t1'
                 | uu____2790 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2807 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2840 =
                   let uu____2841 = FStar_Syntax_Subst.compress t1'  in
                   uu____2841.FStar_Syntax_Syntax.n  in
                 match uu____2840 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2858 -> aux true t1'
                 | uu____2865 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2882 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2931 =
                   let uu____2932 = FStar_Syntax_Subst.compress t1'  in
                   uu____2932.FStar_Syntax_Syntax.n  in
                 match uu____2931 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2949 -> aux true t1'
                 | uu____2956 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2973 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2990 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3007 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3024 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3041 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3072 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3107 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3130 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3159 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3188 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3227 ->
              let uu____3234 =
                let uu____3235 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3236 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3235 uu____3236
                 in
              failwith uu____3234
          | FStar_Syntax_Syntax.Tm_ascribed uu____3251 ->
              let uu____3278 =
                let uu____3279 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3280 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3279 uu____3280
                 in
              failwith uu____3278
          | FStar_Syntax_Syntax.Tm_delayed uu____3295 ->
              let uu____3318 =
                let uu____3319 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3320 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3319 uu____3320
                 in
              failwith uu____3318
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3335 =
                let uu____3336 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3337 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3336 uu____3337
                 in
              failwith uu____3335
           in
        let uu____3352 = whnf env t1  in aux false uu____3352
  
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
      let uu____3408 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3408 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3448 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3448, FStar_Syntax_Util.t_true)
  
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
        let uu____3472 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3472 with
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
  fun uu____3551  ->
    match uu____3551 with
    | (t_base,refopt) ->
        let uu____3582 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3582 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3620 =
      let uu____3623 =
        let uu____3626 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3649  ->
                  match uu____3649 with | (uu____3656,uu____3657,x) -> x))
           in
        FStar_List.append wl.attempting uu____3626  in
      FStar_List.map (wl_prob_to_string wl) uu____3623  in
    FStar_All.pipe_right uu____3620 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____3671 .
    ('Auu____3671,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3682  ->
    match uu____3682 with
    | (uu____3689,c,args) ->
        let uu____3692 = print_ctx_uvar c  in
        let uu____3693 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3692 uu____3693
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3699 = FStar_Syntax_Util.head_and_args t  in
    match uu____3699 with
    | (head1,_args) ->
        let uu____3742 =
          let uu____3743 = FStar_Syntax_Subst.compress head1  in
          uu____3743.FStar_Syntax_Syntax.n  in
        (match uu____3742 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3746 -> true
         | uu____3759 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3765 = FStar_Syntax_Util.head_and_args t  in
    match uu____3765 with
    | (head1,_args) ->
        let uu____3808 =
          let uu____3809 = FStar_Syntax_Subst.compress head1  in
          uu____3809.FStar_Syntax_Syntax.n  in
        (match uu____3808 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____3813) -> u
         | uu____3830 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____3853 = FStar_Syntax_Util.head_and_args t  in
      match uu____3853 with
      | (head1,args) ->
          let uu____3900 =
            let uu____3901 = FStar_Syntax_Subst.compress head1  in
            uu____3901.FStar_Syntax_Syntax.n  in
          (match uu____3900 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____3909)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____3942 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___329_3967  ->
                         match uu___329_3967 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____3971 =
                               let uu____3972 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____3972.FStar_Syntax_Syntax.n  in
                             (match uu____3971 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____3976 -> false)
                         | uu____3977 -> true))
                  in
               (match uu____3942 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4001 =
                        FStar_List.collect
                          (fun uu___330_4013  ->
                             match uu___330_4013 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4017 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4017]
                             | uu____4018 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4001 FStar_List.rev  in
                    let uu____4041 =
                      let uu____4048 =
                        let uu____4057 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___331_4079  ->
                                  match uu___331_4079 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4083 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4083]
                                  | uu____4084 -> []))
                           in
                        FStar_All.pipe_right uu____4057 FStar_List.rev  in
                      let uu____4107 =
                        let uu____4110 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4110  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4048 uu____4107
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4041 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4145  ->
                                match uu____4145 with
                                | (x,i) ->
                                    let uu____4164 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4164, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4195  ->
                                match uu____4195 with
                                | (a,i) ->
                                    let uu____4214 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4214, i)) args_sol
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
           | uu____4236 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4256 =
          let uu____4279 =
            let uu____4280 = FStar_Syntax_Subst.compress k  in
            uu____4280.FStar_Syntax_Syntax.n  in
          match uu____4279 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4361 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4361)
              else
                (let uu____4395 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4395 with
                 | (ys',t1,uu____4428) ->
                     let uu____4433 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4433))
          | uu____4472 ->
              let uu____4473 =
                let uu____4478 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4478)  in
              ((ys, t), uu____4473)
           in
        match uu____4256 with
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
                 let uu____4571 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4571 c  in
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
               (let uu____4645 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4645
                then
                  let uu____4646 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4647 = print_ctx_uvar uv  in
                  let uu____4648 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4646 uu____4647 uu____4648
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4654 =
                   let uu____4655 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4655  in
                 let uu____4656 =
                   let uu____4659 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4659
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____4654 uu____4656 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____4692 =
               let uu____4693 =
                 let uu____4694 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____4695 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____4694 uu____4695
                  in
               failwith uu____4693  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____4759  ->
                       match uu____4759 with
                       | (a,i) ->
                           let uu____4780 =
                             let uu____4781 = FStar_Syntax_Subst.compress a
                                in
                             uu____4781.FStar_Syntax_Syntax.n  in
                           (match uu____4780 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____4807 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____4817 =
                 let uu____4818 = is_flex g  in Prims.op_Negation uu____4818
                  in
               if uu____4817
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____4822 = destruct_flex_t g wl  in
                  match uu____4822 with
                  | ((uu____4827,uv1,args),wl1) ->
                      ((let uu____4832 = args_as_binders args  in
                        assign_solution uu____4832 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___355_4834 = wl1  in
              {
                attempting = (uu___355_4834.attempting);
                wl_deferred = (uu___355_4834.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___355_4834.defer_ok);
                smt_ok = (uu___355_4834.smt_ok);
                tcenv = (uu___355_4834.tcenv);
                wl_implicits = (uu___355_4834.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4855 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4855
         then
           let uu____4856 = FStar_Util.string_of_int pid  in
           let uu____4857 =
             let uu____4858 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4858 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4856 uu____4857
         else ());
        commit sol;
        (let uu___356_4865 = wl  in
         {
           attempting = (uu___356_4865.attempting);
           wl_deferred = (uu___356_4865.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___356_4865.defer_ok);
           smt_ok = (uu___356_4865.smt_ok);
           tcenv = (uu___356_4865.tcenv);
           wl_implicits = (uu___356_4865.wl_implicits)
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
             | (uu____4927,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4955 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4955
              in
           (let uu____4961 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4961
            then
              let uu____4962 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4963 =
                let uu____4964 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4964 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4962 uu____4963
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
        let uu____4989 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4989 FStar_Util.set_elements  in
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
      let uu____5023 = occurs uk t  in
      match uu____5023 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5052 =
                 let uu____5053 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5054 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5053 uu____5054
                  in
               FStar_Pervasives_Native.Some uu____5052)
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
            let uu____5167 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5167 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5217 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5273  ->
             match uu____5273 with
             | (x,uu____5285) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5302 = FStar_List.last bs  in
      match uu____5302 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5326) ->
          let uu____5337 =
            FStar_Util.prefix_until
              (fun uu___332_5352  ->
                 match uu___332_5352 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5354 -> false) g
             in
          (match uu____5337 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5367,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5403 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5403 with
        | (pfx,uu____5413) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5425 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5425 with
             | (uu____5432,src',wl1) ->
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
                 | uu____5544 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5545 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5609  ->
                  fun uu____5610  ->
                    match (uu____5609, uu____5610) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5713 =
                          let uu____5714 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5714
                           in
                        if uu____5713
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5743 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5743
                           then
                             let uu____5758 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5758)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5545 with | (isect,uu____5807) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5842 'Auu____5843 .
    (FStar_Syntax_Syntax.bv,'Auu____5842) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5843) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5900  ->
              fun uu____5901  ->
                match (uu____5900, uu____5901) with
                | ((a,uu____5919),(b,uu____5921)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5936 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5936) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5966  ->
           match uu____5966 with
           | (y,uu____5972) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5981 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5981) FStar_Pervasives_Native.tuple2
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
                   let uu____6143 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6143
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6173 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6220 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6258 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6271 -> false
  
let string_of_option :
  'Auu____6278 .
    ('Auu____6278 -> Prims.string) ->
      'Auu____6278 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___333_6293  ->
      match uu___333_6293 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6299 = f x  in Prims.strcat "Some " uu____6299
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___334_6304  ->
    match uu___334_6304 with
    | MisMatch (d1,d2) ->
        let uu____6315 =
          let uu____6316 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6317 =
            let uu____6318 =
              let uu____6319 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6319 ")"  in
            Prims.strcat ") (" uu____6318  in
          Prims.strcat uu____6316 uu____6317  in
        Prims.strcat "MisMatch (" uu____6315
    | HeadMatch u ->
        let uu____6321 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6321
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___335_6326  ->
    match uu___335_6326 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6341 -> HeadMatch false
  
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
          let uu____6355 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6355 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6366 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6389 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6398 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6424 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6424
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6425 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6426 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6427 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6440 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6453 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6477) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6483,uu____6484) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6526) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6551;
             FStar_Syntax_Syntax.index = uu____6552;
             FStar_Syntax_Syntax.sort = t2;_},uu____6554)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6561 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6562 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6563 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6578 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6585 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6605 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6605
  
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
           { FStar_Syntax_Syntax.blob = uu____6623;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6624;
             FStar_Syntax_Syntax.ltyp = uu____6625;
             FStar_Syntax_Syntax.rng = uu____6626;_},uu____6627)
            ->
            let uu____6638 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____6638 t21
        | (uu____6639,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____6640;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6641;
             FStar_Syntax_Syntax.ltyp = uu____6642;
             FStar_Syntax_Syntax.rng = uu____6643;_})
            ->
            let uu____6654 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____6654
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____6664 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6664
            then FullMatch
            else
              (let uu____6666 =
                 let uu____6675 =
                   let uu____6678 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6678  in
                 let uu____6679 =
                   let uu____6682 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6682  in
                 (uu____6675, uu____6679)  in
               MisMatch uu____6666)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6688),FStar_Syntax_Syntax.Tm_uinst (g,uu____6690)) ->
            let uu____6699 = head_matches env f g  in
            FStar_All.pipe_right uu____6699 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6702 = FStar_Const.eq_const c d  in
            if uu____6702
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6709),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6711)) ->
            let uu____6744 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6744
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6751),FStar_Syntax_Syntax.Tm_refine (y,uu____6753)) ->
            let uu____6762 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6762 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6764),uu____6765) ->
            let uu____6770 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6770 head_match
        | (uu____6771,FStar_Syntax_Syntax.Tm_refine (x,uu____6773)) ->
            let uu____6778 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6778 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6779,FStar_Syntax_Syntax.Tm_type
           uu____6780) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6781,FStar_Syntax_Syntax.Tm_arrow uu____6782) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6812),FStar_Syntax_Syntax.Tm_app (head',uu____6814))
            ->
            let uu____6863 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6863 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6865),uu____6866) ->
            let uu____6891 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6891 head_match
        | (uu____6892,FStar_Syntax_Syntax.Tm_app (head1,uu____6894)) ->
            let uu____6919 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6919 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6920,FStar_Syntax_Syntax.Tm_let
           uu____6921) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6946,FStar_Syntax_Syntax.Tm_match uu____6947) ->
            HeadMatch true
        | uu____6992 ->
            let uu____6997 =
              let uu____7006 = delta_depth_of_term env t11  in
              let uu____7009 = delta_depth_of_term env t21  in
              (uu____7006, uu____7009)  in
            MisMatch uu____6997
  
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
          (let uu____7069 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7069
           then
             let uu____7070 = FStar_Syntax_Print.term_to_string t  in
             let uu____7071 = FStar_Syntax_Print.term_to_string head1  in
             FStar_Util.print2 "Head of %s is %s\n" uu____7070 uu____7071
           else ());
          (let uu____7073 =
             let uu____7074 = FStar_Syntax_Util.un_uinst head1  in
             uu____7074.FStar_Syntax_Syntax.n  in
           match uu____7073 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____7080 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant;
                   FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____7080 with
                | FStar_Pervasives_Native.None  ->
                    ((let uu____7094 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7094
                      then
                        let uu____7095 =
                          FStar_Syntax_Print.term_to_string head1  in
                        FStar_Util.print1 "No definition found for %s\n"
                          uu____7095
                      else ());
                     FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.Some uu____7097 ->
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
                    ((let uu____7108 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7108
                      then
                        let uu____7109 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____7110 = FStar_Syntax_Print.term_to_string t'
                           in
                        FStar_Util.print2 "Inlined %s to %s\n" uu____7109
                          uu____7110
                      else ());
                     FStar_Pervasives_Native.Some t'))
           | uu____7112 -> FStar_Pervasives_Native.None)
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
          (let uu____7250 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7250
           then
             let uu____7251 = FStar_Syntax_Print.term_to_string t11  in
             let uu____7252 = FStar_Syntax_Print.term_to_string t21  in
             let uu____7253 = string_of_match_result r  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7251
               uu____7252 uu____7253
           else ());
          (let reduce_one_and_try_again d1 d2 =
             let d1_greater_than_d2 =
               FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
             let uu____7277 =
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
             match uu____7277 with
             | (t12,t22) ->
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           let reduce_both_and_try_again d r1 =
             let uu____7322 = FStar_TypeChecker_Common.decr_delta_depth d  in
             match uu____7322 with
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
                uu____7354),uu____7355)
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7373 =
                    let uu____7382 = maybe_inline t11  in
                    let uu____7385 = maybe_inline t21  in
                    (uu____7382, uu____7385)  in
                  match uu____7373 with
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
               (uu____7422,FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level uu____7423))
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7441 =
                    let uu____7450 = maybe_inline t11  in
                    let uu____7453 = maybe_inline t21  in
                    (uu____7450, uu____7453)  in
                  match uu____7441 with
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
           | MisMatch uu____7502 -> fail1 n_delta r t11 t21
           | uu____7511 -> success n_delta r t11 t21)
           in
        let r = aux true (Prims.parse_int "0") t1 t2  in
        (let uu____7524 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelDelta")
            in
         if uu____7524
         then
           let uu____7525 = FStar_Syntax_Print.term_to_string t1  in
           let uu____7526 = FStar_Syntax_Print.term_to_string t2  in
           let uu____7527 =
             string_of_match_result (FStar_Pervasives_Native.fst r)  in
           let uu____7534 =
             if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
             then "None"
             else
               (let uu____7546 =
                  FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____7546
                  (fun uu____7580  ->
                     match uu____7580 with
                     | (t11,t21) ->
                         let uu____7587 =
                           FStar_Syntax_Print.term_to_string t11  in
                         let uu____7588 =
                           let uu____7589 =
                             FStar_Syntax_Print.term_to_string t21  in
                           Prims.strcat "; " uu____7589  in
                         Prims.strcat uu____7587 uu____7588))
              in
           FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
             uu____7525 uu____7526 uu____7527 uu____7534
         else ());
        r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7601 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7601 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___336_7614  ->
    match uu___336_7614 with
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
      let uu___357_7651 = p  in
      let uu____7654 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7655 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___357_7651.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7654;
        FStar_TypeChecker_Common.relation =
          (uu___357_7651.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7655;
        FStar_TypeChecker_Common.element =
          (uu___357_7651.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___357_7651.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___357_7651.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___357_7651.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___357_7651.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___357_7651.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7669 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7669
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7674 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7696 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7696 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7704 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7704 with
           | (lh,lhs_args) ->
               let uu____7751 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7751 with
                | (rh,rhs_args) ->
                    let uu____7798 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7811,FStar_Syntax_Syntax.Tm_uvar uu____7812)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7901 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7928,uu____7929)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7944,FStar_Syntax_Syntax.Tm_uvar uu____7945)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7960,FStar_Syntax_Syntax.Tm_arrow uu____7961)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_7991 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_7991.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_7991.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_7991.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_7991.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_7991.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_7991.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_7991.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_7991.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_7991.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7994,FStar_Syntax_Syntax.Tm_type uu____7995)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_8011 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_8011.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_8011.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_8011.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_8011.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_8011.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_8011.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_8011.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_8011.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_8011.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8014,FStar_Syntax_Syntax.Tm_uvar uu____8015)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_8031 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_8031.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_8031.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_8031.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_8031.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_8031.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_8031.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_8031.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_8031.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_8031.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8034,FStar_Syntax_Syntax.Tm_uvar uu____8035)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8050,uu____8051)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8066,FStar_Syntax_Syntax.Tm_uvar uu____8067)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8082,uu____8083) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7798 with
                     | (rank,tp1) ->
                         let uu____8096 =
                           FStar_All.pipe_right
                             (let uu___359_8100 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___359_8100.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___359_8100.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___359_8100.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___359_8100.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___359_8100.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___359_8100.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___359_8100.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___359_8100.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___359_8100.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____8096))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8106 =
            FStar_All.pipe_right
              (let uu___360_8110 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___360_8110.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___360_8110.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___360_8110.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___360_8110.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___360_8110.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___360_8110.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___360_8110.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___360_8110.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___360_8110.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8106)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8171 probs =
      match uu____8171 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8252 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8273 = rank wl.tcenv hd1  in
               (match uu____8273 with
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
                      (let uu____8332 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8336 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8336)
                          in
                       if uu____8332
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
          let uu____8404 = FStar_Syntax_Util.head_and_args t  in
          match uu____8404 with
          | (hd1,uu____8422) ->
              let uu____8447 =
                let uu____8448 = FStar_Syntax_Subst.compress hd1  in
                uu____8448.FStar_Syntax_Syntax.n  in
              (match uu____8447 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8452) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8486  ->
                           match uu____8486 with
                           | (y,uu____8494) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8516  ->
                                       match uu____8516 with
                                       | (x,uu____8524) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8529 -> false)
           in
        let uu____8530 = rank tcenv p  in
        match uu____8530 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8537 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8564 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8578 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8592 -> false
  
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
                        let uu____8644 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8644 with
                        | (k,uu____8650) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8660 -> false)))
            | uu____8661 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8713 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8719 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8719 = (Prims.parse_int "0")))
                           in
                        if uu____8713 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8735 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8741 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8741 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8735)
               in
            let uu____8742 = filter1 u12  in
            let uu____8745 = filter1 u22  in (uu____8742, uu____8745)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8774 = filter_out_common_univs us1 us2  in
                (match uu____8774 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8833 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8833 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8836 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8846 =
                          let uu____8847 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8848 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8847
                            uu____8848
                           in
                        UFailed uu____8846))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8872 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8872 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8898 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8898 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8901 ->
                let uu____8906 =
                  let uu____8907 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8908 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8907
                    uu____8908 msg
                   in
                UFailed uu____8906
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8909,uu____8910) ->
              let uu____8911 =
                let uu____8912 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8913 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8912 uu____8913
                 in
              failwith uu____8911
          | (FStar_Syntax_Syntax.U_unknown ,uu____8914) ->
              let uu____8915 =
                let uu____8916 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8917 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8916 uu____8917
                 in
              failwith uu____8915
          | (uu____8918,FStar_Syntax_Syntax.U_bvar uu____8919) ->
              let uu____8920 =
                let uu____8921 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8922 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8921 uu____8922
                 in
              failwith uu____8920
          | (uu____8923,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8924 =
                let uu____8925 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8926 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8925 uu____8926
                 in
              failwith uu____8924
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8950 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8950
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8964 = occurs_univ v1 u3  in
              if uu____8964
              then
                let uu____8965 =
                  let uu____8966 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8967 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8966 uu____8967
                   in
                try_umax_components u11 u21 uu____8965
              else
                (let uu____8969 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8969)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8981 = occurs_univ v1 u3  in
              if uu____8981
              then
                let uu____8982 =
                  let uu____8983 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8984 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8983 uu____8984
                   in
                try_umax_components u11 u21 uu____8982
              else
                (let uu____8986 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8986)
          | (FStar_Syntax_Syntax.U_max uu____8987,uu____8988) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8994 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8994
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8996,FStar_Syntax_Syntax.U_max uu____8997) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9003 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9003
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9005,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9006,FStar_Syntax_Syntax.U_name
             uu____9007) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9008) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9009) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9010,FStar_Syntax_Syntax.U_succ
             uu____9011) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9012,FStar_Syntax_Syntax.U_zero
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
      let uu____9112 = bc1  in
      match uu____9112 with
      | (bs1,mk_cod1) ->
          let uu____9156 = bc2  in
          (match uu____9156 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9267 = aux xs ys  in
                     (match uu____9267 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9350 =
                       let uu____9357 = mk_cod1 xs  in ([], uu____9357)  in
                     let uu____9360 =
                       let uu____9367 = mk_cod2 ys  in ([], uu____9367)  in
                     (uu____9350, uu____9360)
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
                  let uu____9435 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9435 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9438 =
                    let uu____9439 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9439 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9438
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9444 = has_type_guard t1 t2  in (uu____9444, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9445 = has_type_guard t2 t1  in (uu____9445, wl)
  
let is_flex_pat :
  'Auu____9454 'Auu____9455 'Auu____9456 .
    ('Auu____9454,'Auu____9455,'Auu____9456 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___337_9469  ->
    match uu___337_9469 with
    | (uu____9478,uu____9479,[]) -> true
    | uu____9482 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9513 = f  in
      match uu____9513 with
      | (uu____9520,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9521;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9522;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9525;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9526;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9527;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9587  ->
                 match uu____9587 with
                 | (y,uu____9595) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9749 =
                  let uu____9764 =
                    let uu____9767 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9767  in
                  ((FStar_List.rev pat_binders), uu____9764)  in
                FStar_Pervasives_Native.Some uu____9749
            | (uu____9800,[]) ->
                let uu____9831 =
                  let uu____9846 =
                    let uu____9849 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9849  in
                  ((FStar_List.rev pat_binders), uu____9846)  in
                FStar_Pervasives_Native.Some uu____9831
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9940 =
                  let uu____9941 = FStar_Syntax_Subst.compress a  in
                  uu____9941.FStar_Syntax_Syntax.n  in
                (match uu____9940 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9961 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9961
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___361_9988 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___361_9988.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___361_9988.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9992 =
                            let uu____9993 =
                              let uu____10000 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____10000)  in
                            FStar_Syntax_Syntax.NT uu____9993  in
                          [uu____9992]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___362_10016 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___362_10016.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___362_10016.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10017 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____10057 =
                  let uu____10072 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10072  in
                (match uu____10057 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10147 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10180 ->
               let uu____10181 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10181 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10465 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10465
       then
         let uu____10466 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10466
       else ());
      (let uu____10468 = next_prob probs  in
       match uu____10468 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___363_10495 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___363_10495.wl_deferred);
               ctr = (uu___363_10495.ctr);
               defer_ok = (uu___363_10495.defer_ok);
               smt_ok = (uu___363_10495.smt_ok);
               tcenv = (uu___363_10495.tcenv);
               wl_implicits = (uu___363_10495.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10503 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10503
                 then
                   let uu____10504 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10504
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
                           (let uu___364_10509 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___364_10509.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___364_10509.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___364_10509.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___364_10509.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___364_10509.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___364_10509.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___364_10509.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___364_10509.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___364_10509.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10531 ->
                let uu____10540 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10599  ->
                          match uu____10599 with
                          | (c,uu____10607,uu____10608) -> c < probs.ctr))
                   in
                (match uu____10540 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10649 =
                            let uu____10654 =
                              FStar_List.map
                                (fun uu____10669  ->
                                   match uu____10669 with
                                   | (uu____10680,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10654, (probs.wl_implicits))  in
                          Success uu____10649
                      | uu____10683 ->
                          let uu____10692 =
                            let uu___365_10693 = probs  in
                            let uu____10694 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10713  ->
                                      match uu____10713 with
                                      | (uu____10720,uu____10721,y) -> y))
                               in
                            {
                              attempting = uu____10694;
                              wl_deferred = rest;
                              ctr = (uu___365_10693.ctr);
                              defer_ok = (uu___365_10693.defer_ok);
                              smt_ok = (uu___365_10693.smt_ok);
                              tcenv = (uu___365_10693.tcenv);
                              wl_implicits = (uu___365_10693.wl_implicits)
                            }  in
                          solve env uu____10692))))

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
            let uu____10728 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10728 with
            | USolved wl1 ->
                let uu____10730 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10730
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
                  let uu____10782 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10782 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10785 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10797;
                  FStar_Syntax_Syntax.vars = uu____10798;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10801;
                  FStar_Syntax_Syntax.vars = uu____10802;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10814,uu____10815) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10822,FStar_Syntax_Syntax.Tm_uinst uu____10823) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10830 -> USolved wl

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
            ((let uu____10840 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10840
              then
                let uu____10841 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10841 msg
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
               let uu____10927 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10927 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10980 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10980
                then
                  let uu____10981 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10982 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10981 uu____10982
                else ());
               (let uu____10984 = head_matches_delta env1 t1 t2  in
                match uu____10984 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____11029 = eq_prob t1 t2 wl2  in
                         (match uu____11029 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11050 ->
                         let uu____11059 = eq_prob t1 t2 wl2  in
                         (match uu____11059 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11108 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11123 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11124 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11123, uu____11124)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11129 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11130 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11129, uu____11130)
                            in
                         (match uu____11108 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11161 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11161 with
                                | (t1_hd,t1_args) ->
                                    let uu____11206 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11206 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11270 =
                                              let uu____11277 =
                                                let uu____11288 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11288 :: t1_args  in
                                              let uu____11305 =
                                                let uu____11314 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11314 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11363  ->
                                                   fun uu____11364  ->
                                                     fun uu____11365  ->
                                                       match (uu____11363,
                                                               uu____11364,
                                                               uu____11365)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11415),
                                                          (a2,uu____11417))
                                                           ->
                                                           let uu____11454 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11454
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11277
                                                uu____11305
                                               in
                                            match uu____11270 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___366_11480 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___366_11480.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___366_11480.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11488 =
                                                  solve env1 wl'  in
                                                (match uu____11488 with
                                                 | Success (uu____11491,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___367_11495
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___367_11495.attempting);
                                                            wl_deferred =
                                                              (uu___367_11495.wl_deferred);
                                                            ctr =
                                                              (uu___367_11495.ctr);
                                                            defer_ok =
                                                              (uu___367_11495.defer_ok);
                                                            smt_ok =
                                                              (uu___367_11495.smt_ok);
                                                            tcenv =
                                                              (uu___367_11495.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11496 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11528 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11528 with
                                | (t1_base,p1_opt) ->
                                    let uu____11575 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11575 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11685 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11685
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
                                               let uu____11733 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11733
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
                                               let uu____11763 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11763
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
                                               let uu____11793 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11793
                                           | uu____11796 -> t_base  in
                                         let uu____11813 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11813 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11827 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11827, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11834 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11834 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11881 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11881 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11928 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11928
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
                              let uu____11952 = combine t11 t21 wl2  in
                              (match uu____11952 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11985 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11985
                                     then
                                       let uu____11986 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11986
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____12025 ts1 =
               match uu____12025 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12088 = pairwise out t wl2  in
                        (match uu____12088 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12124 =
               let uu____12135 = FStar_List.hd ts  in (uu____12135, [], wl1)
                in
             let uu____12144 = FStar_List.tl ts  in
             aux uu____12124 uu____12144  in
           let uu____12151 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12151 with
           | (this_flex,this_rigid) ->
               let uu____12175 =
                 let uu____12176 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12176.FStar_Syntax_Syntax.n  in
               (match uu____12175 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12201 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12201
                    then
                      let uu____12202 = destruct_flex_t this_flex wl  in
                      (match uu____12202 with
                       | (flex,wl1) ->
                           let uu____12209 = quasi_pattern env flex  in
                           (match uu____12209 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12227 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12227
                                  then
                                    let uu____12228 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12228
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12231 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___368_12234 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___368_12234.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___368_12234.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___368_12234.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___368_12234.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___368_12234.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___368_12234.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___368_12234.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___368_12234.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___368_12234.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12231)
                | uu____12235 ->
                    ((let uu____12237 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12237
                      then
                        let uu____12238 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12238
                      else ());
                     (let uu____12240 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12240 with
                      | (u,_args) ->
                          let uu____12283 =
                            let uu____12284 = FStar_Syntax_Subst.compress u
                               in
                            uu____12284.FStar_Syntax_Syntax.n  in
                          (match uu____12283 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12311 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12311 with
                                 | (u',uu____12329) ->
                                     let uu____12354 =
                                       let uu____12355 = whnf env u'  in
                                       uu____12355.FStar_Syntax_Syntax.n  in
                                     (match uu____12354 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12376 -> false)
                                  in
                               let uu____12377 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___338_12400  ->
                                         match uu___338_12400 with
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
                                              | uu____12409 -> false)
                                         | uu____12412 -> false))
                                  in
                               (match uu____12377 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12426 = whnf env this_rigid
                                         in
                                      let uu____12427 =
                                        FStar_List.collect
                                          (fun uu___339_12433  ->
                                             match uu___339_12433 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12439 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12439]
                                             | uu____12441 -> [])
                                          bounds_probs
                                         in
                                      uu____12426 :: uu____12427  in
                                    let uu____12442 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12442 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12473 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12488 =
                                               let uu____12489 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12489.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12488 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12501 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12501)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12510 -> bound  in
                                           let uu____12511 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12511)  in
                                         (match uu____12473 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12540 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12540
                                                then
                                                  let wl'1 =
                                                    let uu___369_12542 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___369_12542.wl_deferred);
                                                      ctr =
                                                        (uu___369_12542.ctr);
                                                      defer_ok =
                                                        (uu___369_12542.defer_ok);
                                                      smt_ok =
                                                        (uu___369_12542.smt_ok);
                                                      tcenv =
                                                        (uu___369_12542.tcenv);
                                                      wl_implicits =
                                                        (uu___369_12542.wl_implicits)
                                                    }  in
                                                  let uu____12543 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12543
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12546 =
                                                  solve_t env eq_prob
                                                    (let uu___370_12548 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___370_12548.wl_deferred);
                                                       ctr =
                                                         (uu___370_12548.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___370_12548.smt_ok);
                                                       tcenv =
                                                         (uu___370_12548.tcenv);
                                                       wl_implicits =
                                                         (uu___370_12548.wl_implicits)
                                                     })
                                                   in
                                                match uu____12546 with
                                                | Success uu____12549 ->
                                                    let wl2 =
                                                      let uu___371_12555 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___371_12555.wl_deferred);
                                                        ctr =
                                                          (uu___371_12555.ctr);
                                                        defer_ok =
                                                          (uu___371_12555.defer_ok);
                                                        smt_ok =
                                                          (uu___371_12555.smt_ok);
                                                        tcenv =
                                                          (uu___371_12555.tcenv);
                                                        wl_implicits =
                                                          (uu___371_12555.wl_implicits)
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
                                                    let uu____12570 =
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
                                                    ((let uu____12581 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12581
                                                      then
                                                        let uu____12582 =
                                                          let uu____12583 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12583
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12582
                                                      else ());
                                                     (let uu____12589 =
                                                        let uu____12604 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12604)
                                                         in
                                                      match uu____12589 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12626))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12652 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12652
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
                                                                  let uu____12669
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12669))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12694 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12694
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
                                                                    let uu____12712
                                                                    =
                                                                    let uu____12717
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12717
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12712
                                                                    [] wl2
                                                                     in
                                                                  let uu____12722
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12722))))
                                                      | uu____12723 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12738 when flip ->
                               let uu____12739 =
                                 let uu____12740 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12741 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12740 uu____12741
                                  in
                               failwith uu____12739
                           | uu____12742 ->
                               let uu____12743 =
                                 let uu____12744 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12745 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12744 uu____12745
                                  in
                               failwith uu____12743)))))

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
                      (fun uu____12779  ->
                         match uu____12779 with
                         | (x,i) ->
                             let uu____12798 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12798, i)) bs_lhs
                     in
                  let uu____12801 = lhs  in
                  match uu____12801 with
                  | (uu____12802,u_lhs,uu____12804) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12901 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12911 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12911, univ)
                             in
                          match uu____12901 with
                          | (k,univ) ->
                              let uu____12918 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12918 with
                               | (uu____12935,u,wl3) ->
                                   let uu____12938 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12938, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12964 =
                              let uu____12977 =
                                let uu____12988 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12988 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____13039  ->
                                   fun uu____13040  ->
                                     match (uu____13039, uu____13040) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13141 =
                                           let uu____13148 =
                                             let uu____13151 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13151
                                              in
                                           copy_uvar u_lhs [] uu____13148 wl2
                                            in
                                         (match uu____13141 with
                                          | (uu____13180,t_a,wl3) ->
                                              let uu____13183 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13183 with
                                               | (uu____13202,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12977
                                ([], wl1)
                               in
                            (match uu____12964 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___372_13258 = ct  in
                                   let uu____13259 =
                                     let uu____13262 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13262
                                      in
                                   let uu____13277 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___372_13258.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___372_13258.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13259;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13277;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___372_13258.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___373_13295 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___373_13295.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___373_13295.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13298 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13298 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13360 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13360 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13371 =
                                          let uu____13376 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13376)  in
                                        TERM uu____13371  in
                                      let uu____13377 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13377 with
                                       | (sub_prob,wl3) ->
                                           let uu____13390 =
                                             let uu____13391 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13391
                                              in
                                           solve env uu____13390))
                             | (x,imp)::formals2 ->
                                 let uu____13413 =
                                   let uu____13420 =
                                     let uu____13423 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13423
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13420 wl1
                                    in
                                 (match uu____13413 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13444 =
                                          let uu____13447 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13447
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13444 u_x
                                         in
                                      let uu____13448 =
                                        let uu____13451 =
                                          let uu____13454 =
                                            let uu____13455 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13455, imp)  in
                                          [uu____13454]  in
                                        FStar_List.append bs_terms
                                          uu____13451
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13448 formals2 wl2)
                              in
                           let uu____13482 = occurs_check u_lhs arrow1  in
                           (match uu____13482 with
                            | (uu____13493,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13504 =
                                    let uu____13505 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13505
                                     in
                                  giveup_or_defer env orig wl uu____13504
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
              (let uu____13534 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13534
               then
                 let uu____13535 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13536 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13535 (rel_to_string (p_rel orig)) uu____13536
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13657 = rhs wl1 scope env1 subst1  in
                     (match uu____13657 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13677 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13677
                            then
                              let uu____13678 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13678
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____13751 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____13751 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___374_13753 = hd1  in
                       let uu____13754 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___374_13753.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___374_13753.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13754
                       }  in
                     let hd21 =
                       let uu___375_13758 = hd2  in
                       let uu____13759 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___375_13758.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___375_13758.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13759
                       }  in
                     let uu____13762 =
                       let uu____13767 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13767
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13762 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13786 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13786
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13790 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13790 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13853 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13853
                                  in
                               ((let uu____13871 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13871
                                 then
                                   let uu____13872 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13873 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13872
                                     uu____13873
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13900 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13933 = aux wl [] env [] bs1 bs2  in
               match uu____13933 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13982 = attempt sub_probs wl2  in
                   solve env uu____13982)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13987 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13987 wl)

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
              let uu____14001 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____14001 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____14035 = lhs1  in
              match uu____14035 with
              | (uu____14038,ctx_u,uu____14040) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____14048 ->
                        let uu____14049 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____14049 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____14096 = quasi_pattern env1 lhs1  in
              match uu____14096 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____14126) ->
                  let uu____14131 = lhs1  in
                  (match uu____14131 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____14145 = occurs_check ctx_u rhs1  in
                       (match uu____14145 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14187 =
                                let uu____14194 =
                                  let uu____14195 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14195
                                   in
                                FStar_Util.Inl uu____14194  in
                              (uu____14187, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14217 =
                                 let uu____14218 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14218  in
                               if uu____14217
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14238 =
                                    let uu____14245 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14245  in
                                  let uu____14250 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14238, uu____14250)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14318  ->
                     match uu____14318 with
                     | (x,i) ->
                         let uu____14337 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14337, i)) bs_lhs
                 in
              let uu____14340 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14340 with
              | (rhs_hd,args) ->
                  let uu____14383 = FStar_Util.prefix args  in
                  (match uu____14383 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14455 = lhs1  in
                       (match uu____14455 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14459 =
                              let uu____14470 =
                                let uu____14477 =
                                  let uu____14480 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14480
                                   in
                                copy_uvar u_lhs [] uu____14477 wl1  in
                              match uu____14470 with
                              | (uu____14507,t_last_arg,wl2) ->
                                  let uu____14510 =
                                    let uu____14517 =
                                      let uu____14518 =
                                        let uu____14527 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14527]  in
                                      FStar_List.append bs_lhs uu____14518
                                       in
                                    copy_uvar u_lhs uu____14517 t_res_lhs wl2
                                     in
                                  (match uu____14510 with
                                   | (uu____14562,lhs',wl3) ->
                                       let uu____14565 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14565 with
                                        | (uu____14582,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14459 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14603 =
                                     let uu____14604 =
                                       let uu____14609 =
                                         let uu____14610 =
                                           let uu____14613 =
                                             let uu____14618 =
                                               let uu____14619 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14619]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14618
                                              in
                                           uu____14613
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14610
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14609)  in
                                     TERM uu____14604  in
                                   [uu____14603]  in
                                 let uu____14646 =
                                   let uu____14653 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14653 with
                                   | (p1,wl3) ->
                                       let uu____14672 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14672 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14646 with
                                  | (sub_probs,wl3) ->
                                      let uu____14703 =
                                        let uu____14704 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14704  in
                                      solve env1 uu____14703))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14737 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14737 with
                | (uu____14754,args) ->
                    (match args with | [] -> false | uu____14788 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14805 =
                  let uu____14806 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14806.FStar_Syntax_Syntax.n  in
                match uu____14805 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14809 -> true
                | uu____14824 -> false  in
              let uu____14825 = quasi_pattern env1 lhs1  in
              match uu____14825 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14836 =
                    let uu____14837 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14837
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14836
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14844 = is_app rhs1  in
                  if uu____14844
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14846 = is_arrow rhs1  in
                     if uu____14846
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14848 =
                          let uu____14849 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14849
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14848))
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
                let uu____14852 = lhs  in
                (match uu____14852 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14856 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14856 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14873 =
                              let uu____14876 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14876
                               in
                            FStar_All.pipe_right uu____14873
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14893 = occurs_check ctx_uv rhs1  in
                          (match uu____14893 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14915 =
                                   let uu____14916 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14916
                                    in
                                 giveup_or_defer env orig wl uu____14915
                               else
                                 (let uu____14918 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14918
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14923 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14923
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14925 =
                                         let uu____14926 =
                                           names_to_string1 fvs2  in
                                         let uu____14927 =
                                           names_to_string1 fvs1  in
                                         let uu____14928 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14926 uu____14927
                                           uu____14928
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14925)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14936 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14940 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14940 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14963 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14963
                             | (FStar_Util.Inl msg,uu____14965) ->
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
                  (let uu____14998 =
                     let uu____15015 = quasi_pattern env lhs  in
                     let uu____15022 = quasi_pattern env rhs  in
                     (uu____15015, uu____15022)  in
                   match uu____14998 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____15065 = lhs  in
                       (match uu____15065 with
                        | ({ FStar_Syntax_Syntax.n = uu____15066;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____15068;_},u_lhs,uu____15070)
                            ->
                            let uu____15073 = rhs  in
                            (match uu____15073 with
                             | (uu____15074,u_rhs,uu____15076) ->
                                 let uu____15077 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____15077
                                 then
                                   let uu____15082 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____15082
                                 else
                                   (let uu____15084 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____15084 with
                                    | (sub_prob,wl1) ->
                                        let uu____15097 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____15097 with
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
                                             let uu____15129 =
                                               let uu____15136 =
                                                 let uu____15139 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____15139
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
                                                 uu____15136
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____15129 with
                                              | (uu____15142,w,wl2) ->
                                                  let w_app =
                                                    let uu____15148 =
                                                      let uu____15153 =
                                                        FStar_List.map
                                                          (fun uu____15164 
                                                             ->
                                                             match uu____15164
                                                             with
                                                             | (z,uu____15172)
                                                                 ->
                                                                 let uu____15177
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____15177)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____15153
                                                       in
                                                    uu____15148
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____15181 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____15181
                                                    then
                                                      let uu____15182 =
                                                        let uu____15185 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____15186 =
                                                          let uu____15189 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____15190 =
                                                            let uu____15193 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____15194 =
                                                              let uu____15197
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____15204
                                                                =
                                                                let uu____15207
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____15214
                                                                  =
                                                                  let uu____15217
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____15217]
                                                                   in
                                                                uu____15207
                                                                  ::
                                                                  uu____15214
                                                                 in
                                                              uu____15197 ::
                                                                uu____15204
                                                               in
                                                            uu____15193 ::
                                                              uu____15194
                                                             in
                                                          uu____15189 ::
                                                            uu____15190
                                                           in
                                                        uu____15185 ::
                                                          uu____15186
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____15182
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____15223 =
                                                          let uu____15228 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____15228)
                                                           in
                                                        TERM uu____15223  in
                                                      let uu____15229 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____15229
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____15234 =
                                                             let uu____15239
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
                                                               uu____15239)
                                                              in
                                                           TERM uu____15234
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____15240 =
                                                      let uu____15241 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____15241
                                                       in
                                                    solve env uu____15240)))))))
                   | uu____15242 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____15306 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15306
            then
              let uu____15307 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15308 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15309 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15310 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15307 uu____15308 uu____15309 uu____15310
            else ());
           (let uu____15313 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15313 with
            | (head1,args1) ->
                let uu____15356 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15356 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15420 =
                         let uu____15421 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15422 = args_to_string args1  in
                         let uu____15425 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15426 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15421 uu____15422 uu____15425 uu____15426
                          in
                       giveup env1 uu____15420 orig
                     else
                       (let uu____15430 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15436 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15436 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15430
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___376_15438 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___376_15438.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___376_15438.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___376_15438.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___376_15438.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___376_15438.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___376_15438.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___376_15438.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___376_15438.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____15440 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____15440 with
                              | USolved wl2 ->
                                  let uu____15442 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____15442
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____15446 = base_and_refinement env1 t1  in
                           match uu____15446 with
                           | (base1,refinement1) ->
                               let uu____15471 = base_and_refinement env1 t2
                                  in
                               (match uu____15471 with
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
                                           let uu____15591 =
                                             FStar_List.fold_right
                                               (fun uu____15631  ->
                                                  fun uu____15632  ->
                                                    match (uu____15631,
                                                            uu____15632)
                                                    with
                                                    | (((a1,uu____15684),
                                                        (a2,uu____15686)),
                                                       (probs,wl2)) ->
                                                        let uu____15735 =
                                                          let uu____15742 =
                                                            p_scope orig  in
                                                          mk_problem wl2
                                                            uu____15742 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15735
                                                         with
                                                         | (prob',wl3) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl3)))
                                               argp ([], wl1)
                                              in
                                           (match uu____15591 with
                                            | (subprobs,wl2) ->
                                                ((let uu____15774 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____15774
                                                  then
                                                    let uu____15775 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____15775
                                                  else ());
                                                 (let formula =
                                                    let uu____15780 =
                                                      FStar_List.map
                                                        (fun p  -> p_guard p)
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____15780
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  let uu____15788 =
                                                    attempt subprobs wl3  in
                                                  solve env1 uu____15788)))
                                         else
                                           (let uu____15790 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____15790 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let uu____15794 =
                                                  FStar_List.fold_right2
                                                    (fun uu____15831  ->
                                                       fun uu____15832  ->
                                                         fun uu____15833  ->
                                                           match (uu____15831,
                                                                   uu____15832,
                                                                   uu____15833)
                                                           with
                                                           | ((a,uu____15877),
                                                              (a',uu____15879),
                                                              (subprobs,wl3))
                                                               ->
                                                               let uu____15912
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 []
                                                                   orig a
                                                                   FStar_TypeChecker_Common.EQ
                                                                   a'
                                                                   FStar_Pervasives_Native.None
                                                                   "index"
                                                                  in
                                                               (match uu____15912
                                                                with
                                                                | (p,wl4) ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                    args1 args2 ([], wl2)
                                                   in
                                                (match uu____15794 with
                                                 | (subprobs,wl3) ->
                                                     ((let uu____15942 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           (FStar_Options.Other
                                                              "Rel")
                                                          in
                                                       if uu____15942
                                                       then
                                                         let uu____15943 =
                                                           FStar_Syntax_Print.list_to_string
                                                             (prob_to_string
                                                                env1)
                                                             subprobs
                                                            in
                                                         FStar_Util.print1
                                                           "Adding subproblems for arguments: %s\n"
                                                           uu____15943
                                                       else ());
                                                      FStar_List.iter
                                                        (def_check_prob
                                                           "solve_t' subprobs")
                                                        subprobs;
                                                      (let formula =
                                                         let uu____15949 =
                                                           FStar_List.map
                                                             p_guard subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____15949
                                                          in
                                                       let wl4 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl3
                                                          in
                                                       let uu____15957 =
                                                         attempt subprobs wl4
                                                          in
                                                       solve env1 uu____15957))))
                                     | uu____15958 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___377_15994 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___377_15994.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___377_15994.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___377_15994.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___377_15994.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___377_15994.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___377_15994.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___377_15994.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___377_15994.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16069 = destruct_flex_t scrutinee wl1  in
             match uu____16069 with
             | ((_t,uv,_args),wl2) ->
                 let tc_annot env2 t =
                   let uu____16095 =
                     env2.FStar_TypeChecker_Env.type_of
                       (let uu___378_16103 = env2  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___378_16103.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___378_16103.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___378_16103.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___378_16103.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___378_16103.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___378_16103.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___378_16103.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___378_16103.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___378_16103.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___378_16103.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___378_16103.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___378_16103.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___378_16103.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___378_16103.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___378_16103.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___378_16103.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___378_16103.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___378_16103.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___378_16103.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___378_16103.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___378_16103.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___378_16103.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___378_16103.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___378_16103.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___378_16103.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___378_16103.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___378_16103.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___378_16103.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___378_16103.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts = true;
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___378_16103.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___378_16103.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___378_16103.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___378_16103.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___378_16103.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___378_16103.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___378_16103.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___378_16103.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___378_16103.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___378_16103.FStar_TypeChecker_Env.dep_graph);
                          FStar_TypeChecker_Env.nbe =
                            (uu___378_16103.FStar_TypeChecker_Env.nbe)
                        }) t
                      in
                   match uu____16095 with | (t1,uu____16109,g) -> (t1, g)  in
                 let uu____16111 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p
                     tc_annot
                    in
                 (match uu____16111 with
                  | (xs,pat_term,uu____16126,uu____16127) ->
                      let uu____16132 =
                        FStar_List.fold_left
                          (fun uu____16155  ->
                             fun x  ->
                               match uu____16155 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____16176 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____16176 with
                                    | (uu____16195,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____16132 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____16216 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____16216 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___379_16232 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___379_16232.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    tcenv = (uu___379_16232.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____16240 = solve env1 wl'  in
                                (match uu____16240 with
                                 | Success (uu____16243,imps) ->
                                     let wl'1 =
                                       let uu___380_16246 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___380_16246.wl_deferred);
                                         ctr = (uu___380_16246.ctr);
                                         defer_ok = (uu___380_16246.defer_ok);
                                         smt_ok = (uu___380_16246.smt_ok);
                                         tcenv = (uu___380_16246.tcenv);
                                         wl_implicits =
                                           (uu___380_16246.wl_implicits)
                                       }  in
                                     let uu____16247 = solve env1 wl'1  in
                                     (match uu____16247 with
                                      | Success (uu____16250,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___381_16254 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___381_16254.attempting);
                                                 wl_deferred =
                                                   (uu___381_16254.wl_deferred);
                                                 ctr = (uu___381_16254.ctr);
                                                 defer_ok =
                                                   (uu___381_16254.defer_ok);
                                                 smt_ok =
                                                   (uu___381_16254.smt_ok);
                                                 tcenv =
                                                   (uu___381_16254.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16255 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16261 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16282 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16282
                 then
                   let uu____16283 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16284 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16283 uu____16284
                 else ());
                (let uu____16286 =
                   let uu____16307 =
                     let uu____16316 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16316)  in
                   let uu____16323 =
                     let uu____16332 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16332)  in
                   (uu____16307, uu____16323)  in
                 match uu____16286 with
                 | ((uu____16361,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16364;
                                   FStar_Syntax_Syntax.vars = uu____16365;_}),
                    (s,t)) ->
                     let uu____16436 =
                       let uu____16437 = is_flex scrutinee  in
                       Prims.op_Negation uu____16437  in
                     if uu____16436
                     then
                       ((let uu____16445 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16445
                         then
                           let uu____16446 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16446
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16458 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16458
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16464 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16464
                           then
                             let uu____16465 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16466 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16465 uu____16466
                           else ());
                          (let pat_discriminates uu___340_16487 =
                             match uu___340_16487 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16502;
                                  FStar_Syntax_Syntax.p = uu____16503;_},FStar_Pervasives_Native.None
                                ,uu____16504) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16517;
                                  FStar_Syntax_Syntax.p = uu____16518;_},FStar_Pervasives_Native.None
                                ,uu____16519) -> true
                             | uu____16544 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16644 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16644 with
                                       | (uu____16645,uu____16646,t') ->
                                           let uu____16664 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____16664 with
                                            | (FullMatch ,uu____16675) ->
                                                true
                                            | (HeadMatch
                                               uu____16688,uu____16689) ->
                                                true
                                            | uu____16702 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16735 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16735
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16740 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16740 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16828,uu____16829) ->
                                       branches1
                                   | uu____16974 -> branches  in
                                 let uu____17029 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17038 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17038 with
                                        | (p,uu____17042,uu____17043) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____17029))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17099 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17099 with
                                | (p,uu____17107,e) ->
                                    ((let uu____17126 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17126
                                      then
                                        let uu____17127 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17128 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17127 uu____17128
                                      else ());
                                     (let uu____17130 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____17130)))))
                 | ((s,t),(uu____17145,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____17148;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17149;_}))
                     ->
                     let uu____17218 =
                       let uu____17219 = is_flex scrutinee  in
                       Prims.op_Negation uu____17219  in
                     if uu____17218
                     then
                       ((let uu____17227 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____17227
                         then
                           let uu____17228 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17228
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17240 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17240
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17246 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17246
                           then
                             let uu____17247 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____17248 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17247 uu____17248
                           else ());
                          (let pat_discriminates uu___340_17269 =
                             match uu___340_17269 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17284;
                                  FStar_Syntax_Syntax.p = uu____17285;_},FStar_Pervasives_Native.None
                                ,uu____17286) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17299;
                                  FStar_Syntax_Syntax.p = uu____17300;_},FStar_Pervasives_Native.None
                                ,uu____17301) -> true
                             | uu____17326 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17426 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17426 with
                                       | (uu____17427,uu____17428,t') ->
                                           let uu____17446 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____17446 with
                                            | (FullMatch ,uu____17457) ->
                                                true
                                            | (HeadMatch
                                               uu____17470,uu____17471) ->
                                                true
                                            | uu____17484 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17517 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17517
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17522 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17522 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17610,uu____17611) ->
                                       branches1
                                   | uu____17756 -> branches  in
                                 let uu____17811 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17820 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17820 with
                                        | (p,uu____17824,uu____17825) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17811))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17881 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17881 with
                                | (p,uu____17889,e) ->
                                    ((let uu____17908 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17908
                                      then
                                        let uu____17909 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17910 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17909 uu____17910
                                      else ());
                                     (let uu____17912 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17912)))))
                 | uu____17925 ->
                     ((let uu____17947 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17947
                       then
                         let uu____17948 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17949 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17948 uu____17949
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____17990 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____17990
            then
              let uu____17991 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17992 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____17993 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17994 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____17991 uu____17992 uu____17993 uu____17994
            else ());
           (let uu____17996 = head_matches_delta env1 t1 t2  in
            match uu____17996 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____18027,uu____18028) ->
                     let rec may_relate head3 =
                       let uu____18055 =
                         let uu____18056 = FStar_Syntax_Subst.compress head3
                            in
                         uu____18056.FStar_Syntax_Syntax.n  in
                       match uu____18055 with
                       | FStar_Syntax_Syntax.Tm_name uu____18059 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18060 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18083;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____18084;
                             FStar_Syntax_Syntax.fv_qual = uu____18085;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18088;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____18089;
                             FStar_Syntax_Syntax.fv_qual = uu____18090;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____18094,uu____18095) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____18137) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____18143) ->
                           may_relate t
                       | uu____18148 -> false  in
                     let uu____18149 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____18149 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____18164 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____18164
                          then
                            let uu____18165 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____18165 with
                             | (guard,wl2) ->
                                 let uu____18172 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____18172)
                          else
                            (let uu____18174 =
                               let uu____18175 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____18176 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               FStar_Util.format2 "head mismatch (%s vs %s)"
                                 uu____18175 uu____18176
                                in
                             giveup env1 uu____18174 orig))
                 | (HeadMatch (true ),uu____18177) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18190 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____18190 with
                        | (guard,wl2) ->
                            let uu____18197 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____18197)
                     else
                       (let uu____18199 =
                          let uu____18200 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____18201 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____18200 uu____18201
                           in
                        giveup env1 uu____18199 orig)
                 | (uu____18202,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___382_18216 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___382_18216.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___382_18216.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___382_18216.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___382_18216.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___382_18216.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___382_18216.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___382_18216.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___382_18216.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18240 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18240
          then
            let uu____18241 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18241
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18246 =
                let uu____18249 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18249  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18246 t1);
             (let uu____18267 =
                let uu____18270 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18270  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18267 t2);
             (let uu____18288 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18288
              then
                let uu____18289 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18290 =
                  let uu____18291 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18292 =
                    let uu____18293 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18293  in
                  Prims.strcat uu____18291 uu____18292  in
                let uu____18294 =
                  let uu____18295 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18296 =
                    let uu____18297 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18297  in
                  Prims.strcat uu____18295 uu____18296  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18289
                  uu____18290 uu____18294
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18300,uu____18301) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18324,FStar_Syntax_Syntax.Tm_delayed uu____18325) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18348,uu____18349) ->
                  let uu____18376 =
                    let uu___383_18377 = problem  in
                    let uu____18378 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___383_18377.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18378;
                      FStar_TypeChecker_Common.relation =
                        (uu___383_18377.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___383_18377.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___383_18377.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___383_18377.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___383_18377.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___383_18377.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___383_18377.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___383_18377.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18376 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18379,uu____18380) ->
                  let uu____18387 =
                    let uu___384_18388 = problem  in
                    let uu____18389 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___384_18388.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18389;
                      FStar_TypeChecker_Common.relation =
                        (uu___384_18388.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___384_18388.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___384_18388.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___384_18388.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___384_18388.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___384_18388.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___384_18388.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___384_18388.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18387 wl
              | (uu____18390,FStar_Syntax_Syntax.Tm_ascribed uu____18391) ->
                  let uu____18418 =
                    let uu___385_18419 = problem  in
                    let uu____18420 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___385_18419.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___385_18419.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___385_18419.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18420;
                      FStar_TypeChecker_Common.element =
                        (uu___385_18419.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___385_18419.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___385_18419.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___385_18419.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___385_18419.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___385_18419.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18418 wl
              | (uu____18421,FStar_Syntax_Syntax.Tm_meta uu____18422) ->
                  let uu____18429 =
                    let uu___386_18430 = problem  in
                    let uu____18431 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___386_18430.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___386_18430.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___386_18430.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18431;
                      FStar_TypeChecker_Common.element =
                        (uu___386_18430.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___386_18430.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___386_18430.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___386_18430.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___386_18430.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___386_18430.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18429 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18433),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18435)) ->
                  let uu____18444 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18444
              | (FStar_Syntax_Syntax.Tm_bvar uu____18445,uu____18446) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18447,FStar_Syntax_Syntax.Tm_bvar uu____18448) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___341_18517 =
                    match uu___341_18517 with
                    | [] -> c
                    | bs ->
                        let uu____18545 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18545
                     in
                  let uu____18556 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18556 with
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
                                    let uu____18705 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18705
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
                  let mk_t t l uu___342_18790 =
                    match uu___342_18790 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18832 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18832 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____18977 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____18978 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____18977
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____18978 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____18979,uu____18980) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19009 -> true
                    | uu____19028 -> false  in
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
                      (let uu____19081 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_19089 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_19089.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_19089.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_19089.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_19089.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_19089.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_19089.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_19089.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_19089.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_19089.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_19089.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_19089.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_19089.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_19089.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_19089.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_19089.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_19089.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_19089.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_19089.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_19089.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_19089.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_19089.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_19089.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_19089.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_19089.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_19089.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_19089.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_19089.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_19089.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_19089.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_19089.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_19089.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_19089.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_19089.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_19089.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_19089.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_19089.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_19089.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___387_19089.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_19089.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19081 with
                       | (uu____19092,ty,uu____19094) ->
                           let uu____19095 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19095)
                     in
                  let uu____19096 =
                    let uu____19113 = maybe_eta t1  in
                    let uu____19120 = maybe_eta t2  in
                    (uu____19113, uu____19120)  in
                  (match uu____19096 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_19162 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_19162.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_19162.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_19162.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_19162.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_19162.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_19162.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_19162.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_19162.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19183 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19183
                       then
                         let uu____19184 = destruct_flex_t not_abs wl  in
                         (match uu____19184 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19199 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19199.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19199.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19199.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19199.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19199.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19199.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19199.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19199.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19221 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19221
                       then
                         let uu____19222 = destruct_flex_t not_abs wl  in
                         (match uu____19222 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19237 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19237.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19237.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19237.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19237.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19237.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19237.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19237.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19237.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19239 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19256,FStar_Syntax_Syntax.Tm_abs uu____19257) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19286 -> true
                    | uu____19305 -> false  in
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
                      (let uu____19358 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_19366 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_19366.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_19366.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_19366.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_19366.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_19366.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_19366.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_19366.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_19366.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_19366.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_19366.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_19366.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_19366.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_19366.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_19366.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_19366.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_19366.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_19366.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_19366.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_19366.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_19366.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_19366.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_19366.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_19366.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_19366.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_19366.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_19366.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_19366.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_19366.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_19366.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_19366.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_19366.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_19366.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_19366.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_19366.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_19366.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_19366.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_19366.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___387_19366.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_19366.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19358 with
                       | (uu____19369,ty,uu____19371) ->
                           let uu____19372 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19372)
                     in
                  let uu____19373 =
                    let uu____19390 = maybe_eta t1  in
                    let uu____19397 = maybe_eta t2  in
                    (uu____19390, uu____19397)  in
                  (match uu____19373 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_19439 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_19439.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_19439.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_19439.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_19439.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_19439.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_19439.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_19439.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_19439.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19460 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19460
                       then
                         let uu____19461 = destruct_flex_t not_abs wl  in
                         (match uu____19461 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19476 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19476.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19476.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19476.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19476.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19476.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19476.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19476.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19476.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19498 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19498
                       then
                         let uu____19499 = destruct_flex_t not_abs wl  in
                         (match uu____19499 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19514 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19514.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19514.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19514.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19514.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19514.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19514.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19514.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19514.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19516 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19545 =
                    let uu____19550 =
                      head_matches_delta env x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19550 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___390_19578 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19578.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19578.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19580 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19580.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19580.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19581,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___390_19595 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19595.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19595.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19597 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19597.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19597.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19598 -> (x1, x2)  in
                  (match uu____19545 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19617 = as_refinement false env t11  in
                       (match uu____19617 with
                        | (x12,phi11) ->
                            let uu____19624 = as_refinement false env t21  in
                            (match uu____19624 with
                             | (x22,phi21) ->
                                 ((let uu____19632 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19632
                                   then
                                     ((let uu____19634 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19635 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19636 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19634
                                         uu____19635 uu____19636);
                                      (let uu____19637 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19638 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19639 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19637
                                         uu____19638 uu____19639))
                                   else ());
                                  (let uu____19641 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19641 with
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
                                         let uu____19709 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19709
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19721 =
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
                                         (let uu____19732 =
                                            let uu____19735 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19735
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19732
                                            (p_guard base_prob));
                                         (let uu____19753 =
                                            let uu____19756 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19756
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19753
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19774 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19774)
                                          in
                                       let has_uvars =
                                         (let uu____19778 =
                                            let uu____19779 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19779
                                             in
                                          Prims.op_Negation uu____19778) ||
                                           (let uu____19783 =
                                              let uu____19784 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19784
                                               in
                                            Prims.op_Negation uu____19783)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19787 =
                                           let uu____19792 =
                                             let uu____19801 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19801]  in
                                           mk_t_problem wl1 uu____19792 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19787 with
                                          | (ref_prob,wl2) ->
                                              let uu____19822 =
                                                solve env1
                                                  (let uu___392_19824 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___392_19824.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___392_19824.smt_ok);
                                                     tcenv =
                                                       (uu___392_19824.tcenv);
                                                     wl_implicits =
                                                       (uu___392_19824.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19822 with
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
                                               | Success uu____19834 ->
                                                   let guard =
                                                     let uu____19842 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19842
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___393_19851 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___393_19851.attempting);
                                                       wl_deferred =
                                                         (uu___393_19851.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___393_19851.defer_ok);
                                                       smt_ok =
                                                         (uu___393_19851.smt_ok);
                                                       tcenv =
                                                         (uu___393_19851.tcenv);
                                                       wl_implicits =
                                                         (uu___393_19851.wl_implicits)
                                                     }  in
                                                   let uu____19852 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19852))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19854,FStar_Syntax_Syntax.Tm_uvar uu____19855) ->
                  let uu____19880 = destruct_flex_t t1 wl  in
                  (match uu____19880 with
                   | (f1,wl1) ->
                       let uu____19887 = destruct_flex_t t2 wl1  in
                       (match uu____19887 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19894;
                    FStar_Syntax_Syntax.pos = uu____19895;
                    FStar_Syntax_Syntax.vars = uu____19896;_},uu____19897),FStar_Syntax_Syntax.Tm_uvar
                 uu____19898) ->
                  let uu____19947 = destruct_flex_t t1 wl  in
                  (match uu____19947 with
                   | (f1,wl1) ->
                       let uu____19954 = destruct_flex_t t2 wl1  in
                       (match uu____19954 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19961,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19962;
                    FStar_Syntax_Syntax.pos = uu____19963;
                    FStar_Syntax_Syntax.vars = uu____19964;_},uu____19965))
                  ->
                  let uu____20014 = destruct_flex_t t1 wl  in
                  (match uu____20014 with
                   | (f1,wl1) ->
                       let uu____20021 = destruct_flex_t t2 wl1  in
                       (match uu____20021 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20028;
                    FStar_Syntax_Syntax.pos = uu____20029;
                    FStar_Syntax_Syntax.vars = uu____20030;_},uu____20031),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20032;
                    FStar_Syntax_Syntax.pos = uu____20033;
                    FStar_Syntax_Syntax.vars = uu____20034;_},uu____20035))
                  ->
                  let uu____20108 = destruct_flex_t t1 wl  in
                  (match uu____20108 with
                   | (f1,wl1) ->
                       let uu____20115 = destruct_flex_t t2 wl1  in
                       (match uu____20115 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20122,uu____20123) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20136 = destruct_flex_t t1 wl  in
                  (match uu____20136 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20143;
                    FStar_Syntax_Syntax.pos = uu____20144;
                    FStar_Syntax_Syntax.vars = uu____20145;_},uu____20146),uu____20147)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20184 = destruct_flex_t t1 wl  in
                  (match uu____20184 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____20191,FStar_Syntax_Syntax.Tm_uvar uu____20192) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____20205,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20206;
                    FStar_Syntax_Syntax.pos = uu____20207;
                    FStar_Syntax_Syntax.vars = uu____20208;_},uu____20209))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20246,FStar_Syntax_Syntax.Tm_arrow uu____20247) ->
                  solve_t' env
                    (let uu___394_20275 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20275.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20275.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20275.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20275.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20275.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20275.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20275.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20275.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20275.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20276;
                    FStar_Syntax_Syntax.pos = uu____20277;
                    FStar_Syntax_Syntax.vars = uu____20278;_},uu____20279),FStar_Syntax_Syntax.Tm_arrow
                 uu____20280) ->
                  solve_t' env
                    (let uu___394_20332 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20332.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20332.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20332.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20332.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20332.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20332.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20332.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20332.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20332.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20333,FStar_Syntax_Syntax.Tm_uvar uu____20334) ->
                  let uu____20347 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20347
              | (uu____20348,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20349;
                    FStar_Syntax_Syntax.pos = uu____20350;
                    FStar_Syntax_Syntax.vars = uu____20351;_},uu____20352))
                  ->
                  let uu____20389 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20389
              | (FStar_Syntax_Syntax.Tm_uvar uu____20390,uu____20391) ->
                  let uu____20404 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20404
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20405;
                    FStar_Syntax_Syntax.pos = uu____20406;
                    FStar_Syntax_Syntax.vars = uu____20407;_},uu____20408),uu____20409)
                  ->
                  let uu____20446 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20446
              | (FStar_Syntax_Syntax.Tm_refine uu____20447,uu____20448) ->
                  let t21 =
                    let uu____20456 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20456  in
                  solve_t env
                    (let uu___395_20482 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___395_20482.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___395_20482.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___395_20482.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___395_20482.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___395_20482.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___395_20482.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___395_20482.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___395_20482.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___395_20482.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20483,FStar_Syntax_Syntax.Tm_refine uu____20484) ->
                  let t11 =
                    let uu____20492 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20492  in
                  solve_t env
                    (let uu___396_20518 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___396_20518.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___396_20518.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___396_20518.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___396_20518.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___396_20518.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___396_20518.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___396_20518.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___396_20518.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___396_20518.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20600 =
                    let uu____20601 = guard_of_prob env wl problem t1 t2  in
                    match uu____20601 with
                    | (guard,wl1) ->
                        let uu____20608 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20608
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20819 = br1  in
                        (match uu____20819 with
                         | (p1,w1,uu____20844) ->
                             let uu____20861 = br2  in
                             (match uu____20861 with
                              | (p2,w2,uu____20880) ->
                                  let uu____20885 =
                                    let uu____20886 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20886  in
                                  if uu____20885
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20902 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20902 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____20935 = br2  in
                                         (match uu____20935 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____20972 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____20972
                                                 in
                                              let uu____20985 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____21008,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____21025) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____21068 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____21068 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____20985
                                                (fun uu____21110  ->
                                                   match uu____21110 with
                                                   | (wprobs,wl2) ->
                                                       let uu____21131 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____21131
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____21146 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____21146
                                                              (fun
                                                                 uu____21170 
                                                                 ->
                                                                 match uu____21170
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____21255 -> FStar_Pervasives_Native.None  in
                  let uu____21292 = solve_branches wl brs1 brs2  in
                  (match uu____21292 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21320 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21320 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____21339 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21339  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21348 =
                              let uu____21349 =
                                attempt sub_probs1
                                  (let uu___397_21351 = wl3  in
                                   {
                                     attempting = (uu___397_21351.attempting);
                                     wl_deferred =
                                       (uu___397_21351.wl_deferred);
                                     ctr = (uu___397_21351.ctr);
                                     defer_ok = (uu___397_21351.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___397_21351.tcenv);
                                     wl_implicits =
                                       (uu___397_21351.wl_implicits)
                                   })
                                 in
                              solve env uu____21349  in
                            (match uu____21348 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21355 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21361,uu____21362) ->
                  let head1 =
                    let uu____21386 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21386
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21432 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21432
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21478 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21478
                    then
                      let uu____21479 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21480 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21481 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21479 uu____21480 uu____21481
                    else ());
                   (let no_free_uvars t =
                      (let uu____21491 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21491) &&
                        (let uu____21495 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21495)
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
                      let uu____21511 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21511 = FStar_Syntax_Util.Equal  in
                    let uu____21512 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21512
                    then
                      let uu____21513 =
                        let uu____21520 = equal t1 t2  in
                        if uu____21520
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21530 = mk_eq2 wl orig t1 t2  in
                           match uu____21530 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21513 with
                      | (guard,wl1) ->
                          let uu____21551 = solve_prob orig guard [] wl1  in
                          solve env uu____21551
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21553,uu____21554) ->
                  let head1 =
                    let uu____21562 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21562
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21608 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21608
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21654 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21654
                    then
                      let uu____21655 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21656 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21657 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21655 uu____21656 uu____21657
                    else ());
                   (let no_free_uvars t =
                      (let uu____21667 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21667) &&
                        (let uu____21671 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21671)
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
                      let uu____21687 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21687 = FStar_Syntax_Util.Equal  in
                    let uu____21688 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21688
                    then
                      let uu____21689 =
                        let uu____21696 = equal t1 t2  in
                        if uu____21696
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21706 = mk_eq2 wl orig t1 t2  in
                           match uu____21706 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21689 with
                      | (guard,wl1) ->
                          let uu____21727 = solve_prob orig guard [] wl1  in
                          solve env uu____21727
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____21729,uu____21730) ->
                  let head1 =
                    let uu____21732 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21732
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21778 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21778
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21824 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21824
                    then
                      let uu____21825 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21826 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21827 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21825 uu____21826 uu____21827
                    else ());
                   (let no_free_uvars t =
                      (let uu____21837 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21837) &&
                        (let uu____21841 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21841)
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
                      let uu____21857 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21857 = FStar_Syntax_Util.Equal  in
                    let uu____21858 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21858
                    then
                      let uu____21859 =
                        let uu____21866 = equal t1 t2  in
                        if uu____21866
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21876 = mk_eq2 wl orig t1 t2  in
                           match uu____21876 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21859 with
                      | (guard,wl1) ->
                          let uu____21897 = solve_prob orig guard [] wl1  in
                          solve env uu____21897
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____21899,uu____21900) ->
                  let head1 =
                    let uu____21902 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21902
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21948 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21948
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21994 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21994
                    then
                      let uu____21995 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21996 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21997 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21995 uu____21996 uu____21997
                    else ());
                   (let no_free_uvars t =
                      (let uu____22007 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22007) &&
                        (let uu____22011 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22011)
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
                      let uu____22027 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22027 = FStar_Syntax_Util.Equal  in
                    let uu____22028 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22028
                    then
                      let uu____22029 =
                        let uu____22036 = equal t1 t2  in
                        if uu____22036
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22046 = mk_eq2 wl orig t1 t2  in
                           match uu____22046 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22029 with
                      | (guard,wl1) ->
                          let uu____22067 = solve_prob orig guard [] wl1  in
                          solve env uu____22067
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____22069,uu____22070) ->
                  let head1 =
                    let uu____22072 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22072
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22118 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22118
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22164 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22164
                    then
                      let uu____22165 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22166 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22167 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22165 uu____22166 uu____22167
                    else ());
                   (let no_free_uvars t =
                      (let uu____22177 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22177) &&
                        (let uu____22181 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22181)
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
                      let uu____22197 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22197 = FStar_Syntax_Util.Equal  in
                    let uu____22198 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22198
                    then
                      let uu____22199 =
                        let uu____22206 = equal t1 t2  in
                        if uu____22206
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22216 = mk_eq2 wl orig t1 t2  in
                           match uu____22216 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22199 with
                      | (guard,wl1) ->
                          let uu____22237 = solve_prob orig guard [] wl1  in
                          solve env uu____22237
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22239,uu____22240) ->
                  let head1 =
                    let uu____22258 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22258
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22304 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22304
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22350 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22350
                    then
                      let uu____22351 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22352 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22353 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22351 uu____22352 uu____22353
                    else ());
                   (let no_free_uvars t =
                      (let uu____22363 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22363) &&
                        (let uu____22367 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22367)
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
                      let uu____22383 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22383 = FStar_Syntax_Util.Equal  in
                    let uu____22384 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22384
                    then
                      let uu____22385 =
                        let uu____22392 = equal t1 t2  in
                        if uu____22392
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22402 = mk_eq2 wl orig t1 t2  in
                           match uu____22402 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22385 with
                      | (guard,wl1) ->
                          let uu____22423 = solve_prob orig guard [] wl1  in
                          solve env uu____22423
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22425,FStar_Syntax_Syntax.Tm_match uu____22426) ->
                  let head1 =
                    let uu____22450 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22450
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22496 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22496
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22542 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22542
                    then
                      let uu____22543 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22544 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22545 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22543 uu____22544 uu____22545
                    else ());
                   (let no_free_uvars t =
                      (let uu____22555 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22555) &&
                        (let uu____22559 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22559)
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
                      let uu____22575 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22575 = FStar_Syntax_Util.Equal  in
                    let uu____22576 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22576
                    then
                      let uu____22577 =
                        let uu____22584 = equal t1 t2  in
                        if uu____22584
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22594 = mk_eq2 wl orig t1 t2  in
                           match uu____22594 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22577 with
                      | (guard,wl1) ->
                          let uu____22615 = solve_prob orig guard [] wl1  in
                          solve env uu____22615
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22617,FStar_Syntax_Syntax.Tm_uinst uu____22618) ->
                  let head1 =
                    let uu____22626 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22626
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22666 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22666
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22706 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22706
                    then
                      let uu____22707 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22708 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22709 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22707 uu____22708 uu____22709
                    else ());
                   (let no_free_uvars t =
                      (let uu____22719 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22719) &&
                        (let uu____22723 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22723)
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
                      let uu____22739 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22739 = FStar_Syntax_Util.Equal  in
                    let uu____22740 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22740
                    then
                      let uu____22741 =
                        let uu____22748 = equal t1 t2  in
                        if uu____22748
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22758 = mk_eq2 wl orig t1 t2  in
                           match uu____22758 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22741 with
                      | (guard,wl1) ->
                          let uu____22779 = solve_prob orig guard [] wl1  in
                          solve env uu____22779
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22781,FStar_Syntax_Syntax.Tm_name uu____22782) ->
                  let head1 =
                    let uu____22784 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22784
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22824 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22824
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22864 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22864
                    then
                      let uu____22865 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22866 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22867 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22865 uu____22866 uu____22867
                    else ());
                   (let no_free_uvars t =
                      (let uu____22877 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22877) &&
                        (let uu____22881 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22881)
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
                      let uu____22897 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22897 = FStar_Syntax_Util.Equal  in
                    let uu____22898 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22898
                    then
                      let uu____22899 =
                        let uu____22906 = equal t1 t2  in
                        if uu____22906
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22916 = mk_eq2 wl orig t1 t2  in
                           match uu____22916 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22899 with
                      | (guard,wl1) ->
                          let uu____22937 = solve_prob orig guard [] wl1  in
                          solve env uu____22937
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22939,FStar_Syntax_Syntax.Tm_constant uu____22940) ->
                  let head1 =
                    let uu____22942 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22942
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22982 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22982
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23022 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23022
                    then
                      let uu____23023 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23024 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23025 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23023 uu____23024 uu____23025
                    else ());
                   (let no_free_uvars t =
                      (let uu____23035 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23035) &&
                        (let uu____23039 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23039)
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
                      let uu____23055 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23055 = FStar_Syntax_Util.Equal  in
                    let uu____23056 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23056
                    then
                      let uu____23057 =
                        let uu____23064 = equal t1 t2  in
                        if uu____23064
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23074 = mk_eq2 wl orig t1 t2  in
                           match uu____23074 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23057 with
                      | (guard,wl1) ->
                          let uu____23095 = solve_prob orig guard [] wl1  in
                          solve env uu____23095
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23097,FStar_Syntax_Syntax.Tm_fvar uu____23098) ->
                  let head1 =
                    let uu____23100 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23100
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23146 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23146
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23192 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23192
                    then
                      let uu____23193 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23194 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23195 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23193 uu____23194 uu____23195
                    else ());
                   (let no_free_uvars t =
                      (let uu____23205 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23205) &&
                        (let uu____23209 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23209)
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
                      let uu____23225 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23225 = FStar_Syntax_Util.Equal  in
                    let uu____23226 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23226
                    then
                      let uu____23227 =
                        let uu____23234 = equal t1 t2  in
                        if uu____23234
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23244 = mk_eq2 wl orig t1 t2  in
                           match uu____23244 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23227 with
                      | (guard,wl1) ->
                          let uu____23265 = solve_prob orig guard [] wl1  in
                          solve env uu____23265
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23267,FStar_Syntax_Syntax.Tm_app uu____23268) ->
                  let head1 =
                    let uu____23286 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23286
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23326 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23326
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23366 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23366
                    then
                      let uu____23367 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23368 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23369 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23367 uu____23368 uu____23369
                    else ());
                   (let no_free_uvars t =
                      (let uu____23379 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23379) &&
                        (let uu____23383 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23383)
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
                      let uu____23399 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23399 = FStar_Syntax_Util.Equal  in
                    let uu____23400 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23400
                    then
                      let uu____23401 =
                        let uu____23408 = equal t1 t2  in
                        if uu____23408
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23418 = mk_eq2 wl orig t1 t2  in
                           match uu____23418 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23401 with
                      | (guard,wl1) ->
                          let uu____23439 = solve_prob orig guard [] wl1  in
                          solve env uu____23439
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23441,FStar_Syntax_Syntax.Tm_let uu____23442) ->
                  let uu____23467 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23467
                  then
                    let uu____23468 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23468
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23470,uu____23471) ->
                  let uu____23484 =
                    let uu____23489 =
                      let uu____23490 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23491 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23492 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23493 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23490 uu____23491 uu____23492 uu____23493
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23489)
                     in
                  FStar_Errors.raise_error uu____23484
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23494,FStar_Syntax_Syntax.Tm_let uu____23495) ->
                  let uu____23508 =
                    let uu____23513 =
                      let uu____23514 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23515 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23516 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23517 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23514 uu____23515 uu____23516 uu____23517
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23513)
                     in
                  FStar_Errors.raise_error uu____23508
                    t1.FStar_Syntax_Syntax.pos
              | uu____23518 -> giveup env "head tag mismatch" orig))))

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
          (let uu____23579 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23579
           then
             let uu____23580 =
               let uu____23581 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23581  in
             let uu____23582 =
               let uu____23583 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23583  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23580 uu____23582
           else ());
          (let uu____23585 =
             let uu____23586 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23586  in
           if uu____23585
           then
             let uu____23587 =
               let uu____23588 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23589 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23588 uu____23589
                in
             giveup env uu____23587 orig
           else
             (let uu____23591 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23591 with
              | (ret_sub_prob,wl1) ->
                  let uu____23598 =
                    FStar_List.fold_right2
                      (fun uu____23635  ->
                         fun uu____23636  ->
                           fun uu____23637  ->
                             match (uu____23635, uu____23636, uu____23637)
                             with
                             | ((a1,uu____23681),(a2,uu____23683),(arg_sub_probs,wl2))
                                 ->
                                 let uu____23716 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____23716 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23598 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____23745 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____23745  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____23753 = attempt sub_probs wl3  in
                       solve env uu____23753)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23776 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23779)::[] -> wp1
              | uu____23804 ->
                  let uu____23815 =
                    let uu____23816 =
                      let uu____23817 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23817  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23816
                     in
                  failwith uu____23815
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23823 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23823]
              | x -> x  in
            let uu____23825 =
              let uu____23836 =
                let uu____23845 =
                  let uu____23846 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23846 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23845  in
              [uu____23836]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23825;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23863 = lift_c1 ()  in solve_eq uu____23863 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___343_23869  ->
                       match uu___343_23869 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23870 -> false))
                in
             let uu____23871 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23901)::uu____23902,(wp2,uu____23904)::uu____23905)
                   -> (wp1, wp2)
               | uu____23978 ->
                   let uu____24003 =
                     let uu____24008 =
                       let uu____24009 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____24010 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____24009 uu____24010
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____24008)
                      in
                   FStar_Errors.raise_error uu____24003
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23871 with
             | (wpc1,wpc2) ->
                 let uu____24017 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____24017
                 then
                   let uu____24020 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____24020 wl
                 else
                   (let uu____24022 =
                      let uu____24029 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____24029  in
                    match uu____24022 with
                    | (c2_decl,qualifiers) ->
                        let uu____24050 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____24050
                        then
                          let c1_repr =
                            let uu____24054 =
                              let uu____24055 =
                                let uu____24056 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____24056  in
                              let uu____24057 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24055 uu____24057
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24054
                             in
                          let c2_repr =
                            let uu____24059 =
                              let uu____24060 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____24061 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24060 uu____24061
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24059
                             in
                          let uu____24062 =
                            let uu____24067 =
                              let uu____24068 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____24069 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____24068 uu____24069
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____24067
                             in
                          (match uu____24062 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____24073 = attempt [prob] wl2  in
                               solve env uu____24073)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____24084 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24084
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____24087 =
                                     let uu____24094 =
                                       let uu____24095 =
                                         let uu____24112 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____24115 =
                                           let uu____24126 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____24135 =
                                             let uu____24146 =
                                               let uu____24155 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____24155
                                                in
                                             [uu____24146]  in
                                           uu____24126 :: uu____24135  in
                                         (uu____24112, uu____24115)  in
                                       FStar_Syntax_Syntax.Tm_app uu____24095
                                        in
                                     FStar_Syntax_Syntax.mk uu____24094  in
                                   uu____24087 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____24206 =
                                    let uu____24213 =
                                      let uu____24214 =
                                        let uu____24231 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____24234 =
                                          let uu____24245 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24254 =
                                            let uu____24265 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24274 =
                                              let uu____24285 =
                                                let uu____24294 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24294
                                                 in
                                              [uu____24285]  in
                                            uu____24265 :: uu____24274  in
                                          uu____24245 :: uu____24254  in
                                        (uu____24231, uu____24234)  in
                                      FStar_Syntax_Syntax.Tm_app uu____24214
                                       in
                                    FStar_Syntax_Syntax.mk uu____24213  in
                                  uu____24206 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24351 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24351
                            then
                              let uu____24352 =
                                let uu____24353 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24353
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24352
                            else ());
                           (let uu____24355 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24355 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24363 =
                                    let uu____24366 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24366
                                     in
                                  solve_prob orig uu____24363 [] wl1  in
                                let uu____24369 = attempt [base_prob] wl2  in
                                solve env uu____24369))))
           in
        let uu____24370 = FStar_Util.physical_equality c1 c2  in
        if uu____24370
        then
          let uu____24371 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24371
        else
          ((let uu____24374 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24374
            then
              let uu____24375 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24376 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24375
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24376
            else ());
           (let uu____24378 =
              let uu____24387 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24390 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24387, uu____24390)  in
            match uu____24378 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24408),FStar_Syntax_Syntax.Total
                    (t2,uu____24410)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24427 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24427 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24428,FStar_Syntax_Syntax.Total uu____24429) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24447),FStar_Syntax_Syntax.Total
                    (t2,uu____24449)) ->
                     let uu____24466 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24466 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24468),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24470)) ->
                     let uu____24487 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24487 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24489),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24491)) ->
                     let uu____24508 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24508 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24509,FStar_Syntax_Syntax.Comp uu____24510) ->
                     let uu____24519 =
                       let uu___398_24522 = problem  in
                       let uu____24525 =
                         let uu____24526 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24526
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24522.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24525;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24522.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24522.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24522.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24522.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24522.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24522.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24522.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24522.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24519 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24527,FStar_Syntax_Syntax.Comp uu____24528) ->
                     let uu____24537 =
                       let uu___398_24540 = problem  in
                       let uu____24543 =
                         let uu____24544 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24544
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24540.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24543;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24540.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24540.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24540.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24540.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24540.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24540.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24540.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24540.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24537 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24545,FStar_Syntax_Syntax.GTotal uu____24546) ->
                     let uu____24555 =
                       let uu___399_24558 = problem  in
                       let uu____24561 =
                         let uu____24562 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24562
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24558.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24558.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24558.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24561;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24558.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24558.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24558.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24558.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24558.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24558.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24555 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24563,FStar_Syntax_Syntax.Total uu____24564) ->
                     let uu____24573 =
                       let uu___399_24576 = problem  in
                       let uu____24579 =
                         let uu____24580 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24580
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24576.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24576.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24576.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24579;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24576.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24576.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24576.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24576.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24576.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24576.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24573 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24581,FStar_Syntax_Syntax.Comp uu____24582) ->
                     let uu____24583 =
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
                     if uu____24583
                     then
                       let uu____24584 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24584 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24588 =
                            let uu____24593 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24593
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24599 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24600 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24599, uu____24600))
                             in
                          match uu____24588 with
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
                           (let uu____24607 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24607
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24609 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24609 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24612 =
                                  let uu____24613 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24614 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24613 uu____24614
                                   in
                                giveup env uu____24612 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24621 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24621 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24662 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24662 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24680 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24708  ->
                match uu____24708 with
                | (u1,u2) ->
                    let uu____24715 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24716 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24715 uu____24716))
         in
      FStar_All.pipe_right uu____24680 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24743,[])) -> "{}"
      | uu____24768 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24791 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____24791
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24794 =
              FStar_List.map
                (fun uu____24804  ->
                   match uu____24804 with
                   | (uu____24809,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24794 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24814 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24814 imps
  
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
                  let uu____24867 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____24867
                  then
                    let uu____24868 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____24869 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24868
                      (rel_to_string rel) uu____24869
                  else "TOP"  in
                let uu____24871 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____24871 with
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
              let uu____24929 =
                let uu____24932 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____24932
                 in
              FStar_Syntax_Syntax.new_bv uu____24929 t1  in
            let uu____24935 =
              let uu____24940 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____24940
               in
            match uu____24935 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____25013 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____25013
              then
                let uu____25014 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____25014
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
          ((let uu____25036 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____25036
            then
              let uu____25037 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____25037
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____25041 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____25041
             then
               let uu____25042 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____25042
             else ());
            (let f2 =
               let uu____25045 =
                 let uu____25046 = FStar_Syntax_Util.unmeta f1  in
                 uu____25046.FStar_Syntax_Syntax.n  in
               match uu____25045 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____25050 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___400_25051 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___400_25051.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___400_25051.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___400_25051.FStar_TypeChecker_Env.implicits)
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
            let uu____25105 =
              let uu____25106 =
                let uu____25107 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____25107;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____25106  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____25105
  
let with_guard_no_simp :
  'Auu____25122 .
    'Auu____25122 ->
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
            let uu____25145 =
              let uu____25146 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____25146;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____25145
  
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
          (let uu____25176 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____25176
           then
             let uu____25177 = FStar_Syntax_Print.term_to_string t1  in
             let uu____25178 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____25177
               uu____25178
           else ());
          (let uu____25180 =
             let uu____25185 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____25185
              in
           match uu____25180 with
           | (prob,wl) ->
               let g =
                 let uu____25193 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____25203  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____25193  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25237 = try_teq true env t1 t2  in
        match uu____25237 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25241 = FStar_TypeChecker_Env.get_range env  in
              let uu____25242 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25241 uu____25242);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25249 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25249
              then
                let uu____25250 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25251 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25252 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25250
                  uu____25251 uu____25252
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
          let uu____25274 = FStar_TypeChecker_Env.get_range env  in
          let uu____25275 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25274 uu____25275
  
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
        (let uu____25300 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25300
         then
           let uu____25301 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25302 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25301 uu____25302
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25305 =
           let uu____25312 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25312 "sub_comp"
            in
         match uu____25305 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25323 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25333  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25323)))
  
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
      fun uu____25378  ->
        match uu____25378 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25421 =
                 let uu____25426 =
                   let uu____25427 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25428 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25427 uu____25428
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25426)  in
               let uu____25429 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25421 uu____25429)
               in
            let equiv1 v1 v' =
              let uu____25441 =
                let uu____25446 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25447 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25446, uu____25447)  in
              match uu____25441 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25466 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25496 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25496 with
                      | FStar_Syntax_Syntax.U_unif uu____25503 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25532  ->
                                    match uu____25532 with
                                    | (u,v') ->
                                        let uu____25541 = equiv1 v1 v'  in
                                        if uu____25541
                                        then
                                          let uu____25544 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25544 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25560 -> []))
               in
            let uu____25565 =
              let wl =
                let uu___401_25569 = empty_worklist env  in
                {
                  attempting = (uu___401_25569.attempting);
                  wl_deferred = (uu___401_25569.wl_deferred);
                  ctr = (uu___401_25569.ctr);
                  defer_ok = false;
                  smt_ok = (uu___401_25569.smt_ok);
                  tcenv = (uu___401_25569.tcenv);
                  wl_implicits = (uu___401_25569.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25587  ->
                      match uu____25587 with
                      | (lb,v1) ->
                          let uu____25594 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25594 with
                           | USolved wl1 -> ()
                           | uu____25596 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25606 =
              match uu____25606 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25615) -> true
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
                      uu____25638,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25640,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25651) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25658,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25666 -> false)
               in
            let uu____25671 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25686  ->
                      match uu____25686 with
                      | (u,v1) ->
                          let uu____25693 = check_ineq (u, v1)  in
                          if uu____25693
                          then true
                          else
                            ((let uu____25696 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____25696
                              then
                                let uu____25697 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____25698 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____25697
                                  uu____25698
                              else ());
                             false)))
               in
            if uu____25671
            then ()
            else
              ((let uu____25702 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25702
                then
                  ((let uu____25704 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25704);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25714 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25714))
                else ());
               (let uu____25724 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25724))
  
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
        let fail1 uu____25791 =
          match uu____25791 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___402_25812 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___402_25812.attempting);
            wl_deferred = (uu___402_25812.wl_deferred);
            ctr = (uu___402_25812.ctr);
            defer_ok;
            smt_ok = (uu___402_25812.smt_ok);
            tcenv = (uu___402_25812.tcenv);
            wl_implicits = (uu___402_25812.wl_implicits)
          }  in
        (let uu____25814 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25814
         then
           let uu____25815 = FStar_Util.string_of_bool defer_ok  in
           let uu____25816 = wl_to_string wl  in
           let uu____25817 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____25815 uu____25816 uu____25817
         else ());
        (let g1 =
           let uu____25820 = solve_and_commit env wl fail1  in
           match uu____25820 with
           | FStar_Pervasives_Native.Some
               (uu____25827::uu____25828,uu____25829) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___403_25854 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___403_25854.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___403_25854.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____25855 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___404_25863 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___404_25863.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___404_25863.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___404_25863.FStar_TypeChecker_Env.implicits)
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
    let uu____25911 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25911 with
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
            let uu___405_26022 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___405_26022.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___405_26022.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___405_26022.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____26023 =
            let uu____26024 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____26024  in
          if uu____26023
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____26032 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____26033 =
                       let uu____26034 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____26034
                        in
                     FStar_Errors.diag uu____26032 uu____26033)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____26038 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____26039 =
                        let uu____26040 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____26040
                         in
                      FStar_Errors.diag uu____26038 uu____26039)
                   else ();
                   (let uu____26043 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____26043
                      "discharge_guard'" env vc1);
                   (let uu____26044 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____26044 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____26051 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26052 =
                                let uu____26053 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____26053
                                 in
                              FStar_Errors.diag uu____26051 uu____26052)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____26058 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26059 =
                                let uu____26060 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____26060
                                 in
                              FStar_Errors.diag uu____26058 uu____26059)
                           else ();
                           (let vcs =
                              let uu____26071 = FStar_Options.use_tactics ()
                                 in
                              if uu____26071
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____26091  ->
                                     (let uu____26093 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a236  -> ())
                                        uu____26093);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____26136  ->
                                              match uu____26136 with
                                              | (env1,goal,opts) ->
                                                  let uu____26152 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____26152, opts)))))
                              else
                                (let uu____26154 =
                                   let uu____26161 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____26161)  in
                                 [uu____26154])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____26194  ->
                                    match uu____26194 with
                                    | (env1,goal,opts) ->
                                        let uu____26204 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____26204 with
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
                                                (let uu____26212 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26213 =
                                                   let uu____26214 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____26215 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____26214 uu____26215
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26212 uu____26213)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____26218 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26219 =
                                                   let uu____26220 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____26220
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26218 uu____26219)
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
      let uu____26234 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26234 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26241 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26241
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26252 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26252 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____26269 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26269 with
      | FStar_Pervasives_Native.Some uu____26275 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26291 = try_teq false env t1 t2  in
        match uu____26291 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
  
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
            let uu____26321 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26321 with
            | FStar_Pervasives_Native.Some uu____26324 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26344 = acc  in
            match uu____26344 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26356 = hd1  in
                     (match uu____26356 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26361;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26369 = unresolved ctx_u  in
                             if uu____26369
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
                                   let r1 = teq_nosmt env1 t tm  in
                                   (if Prims.op_Negation r1
                                    then
                                      failwith
                                        "resolve_implicits: unifying with an unresolved uvar failed?"
                                    else ();
                                    (let hd2 =
                                       let uu___406_26385 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___406_26385.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           (uu___406_26385.FStar_TypeChecker_Env.imp_uvar);
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___406_26385.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___406_26385.FStar_TypeChecker_Env.imp_range);
                                         FStar_TypeChecker_Env.imp_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     until_fixpoint (out, changed) (hd2 ::
                                       tl1)))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___407_26393 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___407_26393.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___407_26393.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___407_26393.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___407_26393.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___407_26393.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___407_26393.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___407_26393.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___407_26393.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___407_26393.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___407_26393.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___407_26393.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___407_26393.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___407_26393.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___407_26393.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___407_26393.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___407_26393.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___407_26393.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___407_26393.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___407_26393.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___407_26393.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___407_26393.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___407_26393.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___407_26393.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___407_26393.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___407_26393.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___407_26393.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___407_26393.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___407_26393.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___407_26393.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___407_26393.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___407_26393.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___407_26393.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___407_26393.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___407_26393.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___407_26393.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___407_26393.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___407_26393.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___407_26393.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___407_26393.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___407_26393.FStar_TypeChecker_Env.dep_graph);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___407_26393.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___408_26396 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___408_26396.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___408_26396.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___408_26396.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___408_26396.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___408_26396.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___408_26396.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___408_26396.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___408_26396.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___408_26396.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___408_26396.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___408_26396.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___408_26396.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___408_26396.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___408_26396.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___408_26396.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___408_26396.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___408_26396.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___408_26396.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___408_26396.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___408_26396.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___408_26396.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___408_26396.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___408_26396.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___408_26396.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___408_26396.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___408_26396.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___408_26396.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___408_26396.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___408_26396.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___408_26396.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___408_26396.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___408_26396.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___408_26396.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___408_26396.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___408_26396.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___408_26396.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___408_26396.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___408_26396.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___408_26396.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___408_26396.FStar_TypeChecker_Env.dep_graph);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___408_26396.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26399 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26399
                                   then
                                     let uu____26400 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26401 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26402 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26403 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26400 uu____26401 uu____26402
                                       reason uu____26403
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___410_26407  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26414 =
                                             let uu____26423 =
                                               let uu____26430 =
                                                 let uu____26431 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26432 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26433 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26431 uu____26432
                                                   uu____26433
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26430, r)
                                                in
                                             [uu____26423]  in
                                           FStar_Errors.add_errors
                                             uu____26414);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___411_26447 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___411_26447.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___411_26447.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___411_26447.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26450 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26460  ->
                                               let uu____26461 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26462 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26463 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26461 uu____26462
                                                 reason uu____26463)) env2 g2
                                         true
                                        in
                                     match uu____26450 with
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
          let uu___412_26465 = g  in
          let uu____26466 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___412_26465.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___412_26465.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___412_26465.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26466
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
        let uu____26500 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26500 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26501 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a237  -> ()) uu____26501
      | imp::uu____26503 ->
          let uu____26506 =
            let uu____26511 =
              let uu____26512 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26513 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26512 uu____26513 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26511)
             in
          FStar_Errors.raise_error uu____26506
            imp.FStar_TypeChecker_Env.imp_range
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___413_26524 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___413_26524.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___413_26524.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___413_26524.FStar_TypeChecker_Env.implicits)
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
        (let uu____26559 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26559
         then
           let uu____26560 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26561 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26560
             uu____26561
         else ());
        (let uu____26563 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26563 with
         | (prob,x,wl) ->
             let g =
               let uu____26582 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26592  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26582  in
             ((let uu____26612 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26612
               then
                 let uu____26613 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26614 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26615 =
                   let uu____26616 = FStar_Util.must g  in
                   guard_to_string env uu____26616  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26613 uu____26614 uu____26615
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
        let uu____26650 = check_subtyping env t1 t2  in
        match uu____26650 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26669 =
              let uu____26670 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____26670 g  in
            FStar_Pervasives_Native.Some uu____26669
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26688 = check_subtyping env t1 t2  in
        match uu____26688 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26707 =
              let uu____26708 =
                let uu____26709 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26709]  in
              FStar_TypeChecker_Env.close_guard env uu____26708 g  in
            FStar_Pervasives_Native.Some uu____26707
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26744 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26744
         then
           let uu____26745 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26746 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26745
             uu____26746
         else ());
        (let uu____26748 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26748 with
         | (prob,x,wl) ->
             let g =
               let uu____26761 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____26771  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26761  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26792 =
                      let uu____26793 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26793]  in
                    FStar_TypeChecker_Env.close_guard env uu____26792 g1  in
                  discharge_guard_nosmt env g2))
  