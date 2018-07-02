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
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____6632 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6632
            then FullMatch
            else
              (let uu____6634 =
                 let uu____6643 =
                   let uu____6646 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6646  in
                 let uu____6647 =
                   let uu____6650 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6650  in
                 (uu____6643, uu____6647)  in
               MisMatch uu____6634)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6656),FStar_Syntax_Syntax.Tm_uinst (g,uu____6658)) ->
            let uu____6667 = head_matches env f g  in
            FStar_All.pipe_right uu____6667 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6670 = FStar_Const.eq_const c d  in
            if uu____6670
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6677),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6679)) ->
            let uu____6712 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6712
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6719),FStar_Syntax_Syntax.Tm_refine (y,uu____6721)) ->
            let uu____6730 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6730 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6732),uu____6733) ->
            let uu____6738 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6738 head_match
        | (uu____6739,FStar_Syntax_Syntax.Tm_refine (x,uu____6741)) ->
            let uu____6746 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6746 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6747,FStar_Syntax_Syntax.Tm_type
           uu____6748) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6749,FStar_Syntax_Syntax.Tm_arrow uu____6750) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6780),FStar_Syntax_Syntax.Tm_app (head',uu____6782))
            ->
            let uu____6831 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6831 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6833),uu____6834) ->
            let uu____6859 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6859 head_match
        | (uu____6860,FStar_Syntax_Syntax.Tm_app (head1,uu____6862)) ->
            let uu____6887 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6887 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6888,FStar_Syntax_Syntax.Tm_let
           uu____6889) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6914,FStar_Syntax_Syntax.Tm_match uu____6915) ->
            HeadMatch true
        | uu____6960 ->
            let uu____6965 =
              let uu____6974 = delta_depth_of_term env t11  in
              let uu____6977 = delta_depth_of_term env t21  in
              (uu____6974, uu____6977)  in
            MisMatch uu____6965
  
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
          (let uu____7037 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7037
           then
             let uu____7038 = FStar_Syntax_Print.term_to_string t  in
             let uu____7039 = FStar_Syntax_Print.term_to_string head1  in
             FStar_Util.print2 "Head of %s is %s\n" uu____7038 uu____7039
           else ());
          (let uu____7041 =
             let uu____7042 = FStar_Syntax_Util.un_uinst head1  in
             uu____7042.FStar_Syntax_Syntax.n  in
           match uu____7041 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____7048 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant;
                   FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____7048 with
                | FStar_Pervasives_Native.None  ->
                    ((let uu____7062 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7062
                      then
                        let uu____7063 =
                          FStar_Syntax_Print.term_to_string head1  in
                        FStar_Util.print1 "No definition found for %s\n"
                          uu____7063
                      else ());
                     FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.Some uu____7065 ->
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
                    ((let uu____7076 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7076
                      then
                        let uu____7077 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____7078 = FStar_Syntax_Print.term_to_string t'
                           in
                        FStar_Util.print2 "Inlined %s to %s\n" uu____7077
                          uu____7078
                      else ());
                     FStar_Pervasives_Native.Some t'))
           | uu____7080 -> FStar_Pervasives_Native.None)
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
          (let uu____7218 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7218
           then
             let uu____7219 = FStar_Syntax_Print.term_to_string t11  in
             let uu____7220 = FStar_Syntax_Print.term_to_string t21  in
             let uu____7221 = string_of_match_result r  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7219
               uu____7220 uu____7221
           else ());
          (let reduce_one_and_try_again d1 d2 =
             let d1_greater_than_d2 =
               FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
             let uu____7245 =
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
             match uu____7245 with
             | (t12,t22) ->
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           let reduce_both_and_try_again d r1 =
             let uu____7290 = FStar_TypeChecker_Common.decr_delta_depth d  in
             match uu____7290 with
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
                uu____7322),uu____7323)
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7341 =
                    let uu____7350 = maybe_inline t11  in
                    let uu____7353 = maybe_inline t21  in
                    (uu____7350, uu____7353)  in
                  match uu____7341 with
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
               (uu____7390,FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level uu____7391))
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7409 =
                    let uu____7418 = maybe_inline t11  in
                    let uu____7421 = maybe_inline t21  in
                    (uu____7418, uu____7421)  in
                  match uu____7409 with
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
           | MisMatch uu____7470 -> fail1 n_delta r t11 t21
           | uu____7479 -> success n_delta r t11 t21)
           in
        let r = aux true (Prims.parse_int "0") t1 t2  in
        (let uu____7492 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelDelta")
            in
         if uu____7492
         then
           let uu____7493 = FStar_Syntax_Print.term_to_string t1  in
           let uu____7494 = FStar_Syntax_Print.term_to_string t2  in
           let uu____7495 =
             string_of_match_result (FStar_Pervasives_Native.fst r)  in
           let uu____7502 =
             if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
             then "None"
             else
               (let uu____7514 =
                  FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____7514
                  (fun uu____7548  ->
                     match uu____7548 with
                     | (t11,t21) ->
                         let uu____7555 =
                           FStar_Syntax_Print.term_to_string t11  in
                         let uu____7556 =
                           let uu____7557 =
                             FStar_Syntax_Print.term_to_string t21  in
                           Prims.strcat "; " uu____7557  in
                         Prims.strcat uu____7555 uu____7556))
              in
           FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
             uu____7493 uu____7494 uu____7495 uu____7502
         else ());
        r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7569 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7569 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___336_7582  ->
    match uu___336_7582 with
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
      let uu___357_7619 = p  in
      let uu____7622 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7623 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___357_7619.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7622;
        FStar_TypeChecker_Common.relation =
          (uu___357_7619.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7623;
        FStar_TypeChecker_Common.element =
          (uu___357_7619.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___357_7619.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___357_7619.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___357_7619.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___357_7619.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___357_7619.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7637 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7637
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7642 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7664 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7664 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7672 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7672 with
           | (lh,lhs_args) ->
               let uu____7719 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7719 with
                | (rh,rhs_args) ->
                    let uu____7766 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7779,FStar_Syntax_Syntax.Tm_uvar uu____7780)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7869 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7896,uu____7897)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7912,FStar_Syntax_Syntax.Tm_uvar uu____7913)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7928,FStar_Syntax_Syntax.Tm_arrow uu____7929)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_7959 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_7959.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_7959.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_7959.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_7959.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_7959.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_7959.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_7959.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_7959.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_7959.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7962,FStar_Syntax_Syntax.Tm_type uu____7963)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_7979 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_7979.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_7979.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_7979.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_7979.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_7979.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_7979.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_7979.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_7979.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_7979.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7982,FStar_Syntax_Syntax.Tm_uvar uu____7983)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_7999 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_7999.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_7999.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_7999.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_7999.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_7999.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_7999.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_7999.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_7999.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_7999.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8002,FStar_Syntax_Syntax.Tm_uvar uu____8003)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8018,uu____8019)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8034,FStar_Syntax_Syntax.Tm_uvar uu____8035)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8050,uu____8051) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7766 with
                     | (rank,tp1) ->
                         let uu____8064 =
                           FStar_All.pipe_right
                             (let uu___359_8068 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___359_8068.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___359_8068.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___359_8068.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___359_8068.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___359_8068.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___359_8068.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___359_8068.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___359_8068.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___359_8068.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____8064))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8074 =
            FStar_All.pipe_right
              (let uu___360_8078 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___360_8078.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___360_8078.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___360_8078.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___360_8078.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___360_8078.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___360_8078.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___360_8078.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___360_8078.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___360_8078.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8074)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8139 probs =
      match uu____8139 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8220 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8241 = rank wl.tcenv hd1  in
               (match uu____8241 with
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
                      (let uu____8300 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8304 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8304)
                          in
                       if uu____8300
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
          let uu____8372 = FStar_Syntax_Util.head_and_args t  in
          match uu____8372 with
          | (hd1,uu____8390) ->
              let uu____8415 =
                let uu____8416 = FStar_Syntax_Subst.compress hd1  in
                uu____8416.FStar_Syntax_Syntax.n  in
              (match uu____8415 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8420) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8454  ->
                           match uu____8454 with
                           | (y,uu____8462) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8484  ->
                                       match uu____8484 with
                                       | (x,uu____8492) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8497 -> false)
           in
        let uu____8498 = rank tcenv p  in
        match uu____8498 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8505 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8532 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8546 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8560 -> false
  
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
                        let uu____8612 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8612 with
                        | (k,uu____8618) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8628 -> false)))
            | uu____8629 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8681 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8687 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8687 = (Prims.parse_int "0")))
                           in
                        if uu____8681 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8703 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8709 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8709 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8703)
               in
            let uu____8710 = filter1 u12  in
            let uu____8713 = filter1 u22  in (uu____8710, uu____8713)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8742 = filter_out_common_univs us1 us2  in
                (match uu____8742 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8801 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8801 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8804 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8814 =
                          let uu____8815 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8816 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8815
                            uu____8816
                           in
                        UFailed uu____8814))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8840 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8840 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8866 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8866 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8869 ->
                let uu____8874 =
                  let uu____8875 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8876 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8875
                    uu____8876 msg
                   in
                UFailed uu____8874
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8877,uu____8878) ->
              let uu____8879 =
                let uu____8880 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8881 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8880 uu____8881
                 in
              failwith uu____8879
          | (FStar_Syntax_Syntax.U_unknown ,uu____8882) ->
              let uu____8883 =
                let uu____8884 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8885 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8884 uu____8885
                 in
              failwith uu____8883
          | (uu____8886,FStar_Syntax_Syntax.U_bvar uu____8887) ->
              let uu____8888 =
                let uu____8889 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8890 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8889 uu____8890
                 in
              failwith uu____8888
          | (uu____8891,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8892 =
                let uu____8893 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8894 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8893 uu____8894
                 in
              failwith uu____8892
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8918 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8918
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8932 = occurs_univ v1 u3  in
              if uu____8932
              then
                let uu____8933 =
                  let uu____8934 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8935 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8934 uu____8935
                   in
                try_umax_components u11 u21 uu____8933
              else
                (let uu____8937 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8937)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8949 = occurs_univ v1 u3  in
              if uu____8949
              then
                let uu____8950 =
                  let uu____8951 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8952 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8951 uu____8952
                   in
                try_umax_components u11 u21 uu____8950
              else
                (let uu____8954 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8954)
          | (FStar_Syntax_Syntax.U_max uu____8955,uu____8956) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8962 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8962
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8964,FStar_Syntax_Syntax.U_max uu____8965) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8971 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8971
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8973,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8974,FStar_Syntax_Syntax.U_name
             uu____8975) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8976) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8977) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8978,FStar_Syntax_Syntax.U_succ
             uu____8979) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8980,FStar_Syntax_Syntax.U_zero
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
      let uu____9080 = bc1  in
      match uu____9080 with
      | (bs1,mk_cod1) ->
          let uu____9124 = bc2  in
          (match uu____9124 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9235 = aux xs ys  in
                     (match uu____9235 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9318 =
                       let uu____9325 = mk_cod1 xs  in ([], uu____9325)  in
                     let uu____9328 =
                       let uu____9335 = mk_cod2 ys  in ([], uu____9335)  in
                     (uu____9318, uu____9328)
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
                  let uu____9403 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9403 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9406 =
                    let uu____9407 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9407 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9406
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9412 = has_type_guard t1 t2  in (uu____9412, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9413 = has_type_guard t2 t1  in (uu____9413, wl)
  
let is_flex_pat :
  'Auu____9422 'Auu____9423 'Auu____9424 .
    ('Auu____9422,'Auu____9423,'Auu____9424 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___337_9437  ->
    match uu___337_9437 with
    | (uu____9446,uu____9447,[]) -> true
    | uu____9450 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9481 = f  in
      match uu____9481 with
      | (uu____9488,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9489;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9490;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9493;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9494;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9495;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9555  ->
                 match uu____9555 with
                 | (y,uu____9563) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9717 =
                  let uu____9732 =
                    let uu____9735 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9735  in
                  ((FStar_List.rev pat_binders), uu____9732)  in
                FStar_Pervasives_Native.Some uu____9717
            | (uu____9768,[]) ->
                let uu____9799 =
                  let uu____9814 =
                    let uu____9817 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9817  in
                  ((FStar_List.rev pat_binders), uu____9814)  in
                FStar_Pervasives_Native.Some uu____9799
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9908 =
                  let uu____9909 = FStar_Syntax_Subst.compress a  in
                  uu____9909.FStar_Syntax_Syntax.n  in
                (match uu____9908 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9929 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9929
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___361_9956 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___361_9956.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___361_9956.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9960 =
                            let uu____9961 =
                              let uu____9968 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9968)  in
                            FStar_Syntax_Syntax.NT uu____9961  in
                          [uu____9960]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___362_9984 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___362_9984.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___362_9984.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9985 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____10025 =
                  let uu____10040 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10040  in
                (match uu____10025 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10115 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10148 ->
               let uu____10149 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10149 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10433 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10433
       then
         let uu____10434 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10434
       else ());
      (let uu____10436 = next_prob probs  in
       match uu____10436 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___363_10463 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___363_10463.wl_deferred);
               ctr = (uu___363_10463.ctr);
               defer_ok = (uu___363_10463.defer_ok);
               smt_ok = (uu___363_10463.smt_ok);
               tcenv = (uu___363_10463.tcenv);
               wl_implicits = (uu___363_10463.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10471 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10471
                 then
                   let uu____10472 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10472
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
                           (let uu___364_10477 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___364_10477.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___364_10477.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___364_10477.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___364_10477.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___364_10477.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___364_10477.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___364_10477.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___364_10477.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___364_10477.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10499 ->
                let uu____10508 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10567  ->
                          match uu____10567 with
                          | (c,uu____10575,uu____10576) -> c < probs.ctr))
                   in
                (match uu____10508 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10617 =
                            let uu____10622 =
                              FStar_List.map
                                (fun uu____10637  ->
                                   match uu____10637 with
                                   | (uu____10648,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10622, (probs.wl_implicits))  in
                          Success uu____10617
                      | uu____10651 ->
                          let uu____10660 =
                            let uu___365_10661 = probs  in
                            let uu____10662 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10681  ->
                                      match uu____10681 with
                                      | (uu____10688,uu____10689,y) -> y))
                               in
                            {
                              attempting = uu____10662;
                              wl_deferred = rest;
                              ctr = (uu___365_10661.ctr);
                              defer_ok = (uu___365_10661.defer_ok);
                              smt_ok = (uu___365_10661.smt_ok);
                              tcenv = (uu___365_10661.tcenv);
                              wl_implicits = (uu___365_10661.wl_implicits)
                            }  in
                          solve env uu____10660))))

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
            let uu____10696 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10696 with
            | USolved wl1 ->
                let uu____10698 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10698
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
                  let uu____10750 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10750 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10753 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10765;
                  FStar_Syntax_Syntax.vars = uu____10766;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10769;
                  FStar_Syntax_Syntax.vars = uu____10770;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10782,uu____10783) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10790,FStar_Syntax_Syntax.Tm_uinst uu____10791) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10798 -> USolved wl

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
            ((let uu____10808 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10808
              then
                let uu____10809 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10809 msg
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
               let uu____10895 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10895 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10948 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10948
                then
                  let uu____10949 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10950 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10949 uu____10950
                else ());
               (let uu____10952 = head_matches_delta env1 t1 t2  in
                match uu____10952 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10997 = eq_prob t1 t2 wl2  in
                         (match uu____10997 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11018 ->
                         let uu____11027 = eq_prob t1 t2 wl2  in
                         (match uu____11027 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11076 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11091 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11092 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11091, uu____11092)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11097 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11098 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11097, uu____11098)
                            in
                         (match uu____11076 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11129 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11129 with
                                | (t1_hd,t1_args) ->
                                    let uu____11174 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11174 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11238 =
                                              let uu____11245 =
                                                let uu____11256 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11256 :: t1_args  in
                                              let uu____11273 =
                                                let uu____11282 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11282 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11331  ->
                                                   fun uu____11332  ->
                                                     fun uu____11333  ->
                                                       match (uu____11331,
                                                               uu____11332,
                                                               uu____11333)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11383),
                                                          (a2,uu____11385))
                                                           ->
                                                           let uu____11422 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11422
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11245
                                                uu____11273
                                               in
                                            match uu____11238 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___366_11448 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___366_11448.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___366_11448.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11456 =
                                                  solve env1 wl'  in
                                                (match uu____11456 with
                                                 | Success (uu____11459,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___367_11463
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___367_11463.attempting);
                                                            wl_deferred =
                                                              (uu___367_11463.wl_deferred);
                                                            ctr =
                                                              (uu___367_11463.ctr);
                                                            defer_ok =
                                                              (uu___367_11463.defer_ok);
                                                            smt_ok =
                                                              (uu___367_11463.smt_ok);
                                                            tcenv =
                                                              (uu___367_11463.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11464 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11496 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11496 with
                                | (t1_base,p1_opt) ->
                                    let uu____11543 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11543 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11653 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11653
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
                                               let uu____11701 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11701
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
                                               let uu____11731 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11731
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
                                               let uu____11761 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11761
                                           | uu____11764 -> t_base  in
                                         let uu____11781 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11781 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11795 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11795, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11802 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11802 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11849 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11849 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11896 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11896
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
                              let uu____11920 = combine t11 t21 wl2  in
                              (match uu____11920 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11953 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11953
                                     then
                                       let uu____11954 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11954
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11993 ts1 =
               match uu____11993 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12056 = pairwise out t wl2  in
                        (match uu____12056 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12092 =
               let uu____12103 = FStar_List.hd ts  in (uu____12103, [], wl1)
                in
             let uu____12112 = FStar_List.tl ts  in
             aux uu____12092 uu____12112  in
           let uu____12119 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12119 with
           | (this_flex,this_rigid) ->
               let uu____12143 =
                 let uu____12144 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12144.FStar_Syntax_Syntax.n  in
               (match uu____12143 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12169 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12169
                    then
                      let uu____12170 = destruct_flex_t this_flex wl  in
                      (match uu____12170 with
                       | (flex,wl1) ->
                           let uu____12177 = quasi_pattern env flex  in
                           (match uu____12177 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12195 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12195
                                  then
                                    let uu____12196 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12196
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12199 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___368_12202 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___368_12202.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___368_12202.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___368_12202.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___368_12202.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___368_12202.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___368_12202.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___368_12202.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___368_12202.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___368_12202.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12199)
                | uu____12203 ->
                    ((let uu____12205 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12205
                      then
                        let uu____12206 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12206
                      else ());
                     (let uu____12208 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12208 with
                      | (u,_args) ->
                          let uu____12251 =
                            let uu____12252 = FStar_Syntax_Subst.compress u
                               in
                            uu____12252.FStar_Syntax_Syntax.n  in
                          (match uu____12251 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12279 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12279 with
                                 | (u',uu____12297) ->
                                     let uu____12322 =
                                       let uu____12323 = whnf env u'  in
                                       uu____12323.FStar_Syntax_Syntax.n  in
                                     (match uu____12322 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12344 -> false)
                                  in
                               let uu____12345 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___338_12368  ->
                                         match uu___338_12368 with
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
                                              | uu____12377 -> false)
                                         | uu____12380 -> false))
                                  in
                               (match uu____12345 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12394 = whnf env this_rigid
                                         in
                                      let uu____12395 =
                                        FStar_List.collect
                                          (fun uu___339_12401  ->
                                             match uu___339_12401 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12407 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12407]
                                             | uu____12409 -> [])
                                          bounds_probs
                                         in
                                      uu____12394 :: uu____12395  in
                                    let uu____12410 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12410 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12441 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12456 =
                                               let uu____12457 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12457.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12456 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12469 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12469)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12478 -> bound  in
                                           let uu____12479 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12479)  in
                                         (match uu____12441 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12508 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12508
                                                then
                                                  let wl'1 =
                                                    let uu___369_12510 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___369_12510.wl_deferred);
                                                      ctr =
                                                        (uu___369_12510.ctr);
                                                      defer_ok =
                                                        (uu___369_12510.defer_ok);
                                                      smt_ok =
                                                        (uu___369_12510.smt_ok);
                                                      tcenv =
                                                        (uu___369_12510.tcenv);
                                                      wl_implicits =
                                                        (uu___369_12510.wl_implicits)
                                                    }  in
                                                  let uu____12511 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12511
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12514 =
                                                  solve_t env eq_prob
                                                    (let uu___370_12516 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___370_12516.wl_deferred);
                                                       ctr =
                                                         (uu___370_12516.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___370_12516.smt_ok);
                                                       tcenv =
                                                         (uu___370_12516.tcenv);
                                                       wl_implicits =
                                                         (uu___370_12516.wl_implicits)
                                                     })
                                                   in
                                                match uu____12514 with
                                                | Success uu____12517 ->
                                                    let wl2 =
                                                      let uu___371_12523 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___371_12523.wl_deferred);
                                                        ctr =
                                                          (uu___371_12523.ctr);
                                                        defer_ok =
                                                          (uu___371_12523.defer_ok);
                                                        smt_ok =
                                                          (uu___371_12523.smt_ok);
                                                        tcenv =
                                                          (uu___371_12523.tcenv);
                                                        wl_implicits =
                                                          (uu___371_12523.wl_implicits)
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
                                                    let uu____12538 =
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
                                                    ((let uu____12549 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12549
                                                      then
                                                        let uu____12550 =
                                                          let uu____12551 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12551
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12550
                                                      else ());
                                                     (let uu____12557 =
                                                        let uu____12572 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12572)
                                                         in
                                                      match uu____12557 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12594))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12620 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12620
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
                                                                  let uu____12637
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12637))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12662 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12662
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
                                                                    let uu____12680
                                                                    =
                                                                    let uu____12685
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12685
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12680
                                                                    [] wl2
                                                                     in
                                                                  let uu____12690
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12690))))
                                                      | uu____12691 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12706 when flip ->
                               let uu____12707 =
                                 let uu____12708 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12709 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12708 uu____12709
                                  in
                               failwith uu____12707
                           | uu____12710 ->
                               let uu____12711 =
                                 let uu____12712 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12713 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12712 uu____12713
                                  in
                               failwith uu____12711)))))

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
                      (fun uu____12747  ->
                         match uu____12747 with
                         | (x,i) ->
                             let uu____12766 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12766, i)) bs_lhs
                     in
                  let uu____12769 = lhs  in
                  match uu____12769 with
                  | (uu____12770,u_lhs,uu____12772) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12869 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12879 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12879, univ)
                             in
                          match uu____12869 with
                          | (k,univ) ->
                              let uu____12886 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12886 with
                               | (uu____12903,u,wl3) ->
                                   let uu____12906 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12906, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12932 =
                              let uu____12945 =
                                let uu____12956 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12956 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____13007  ->
                                   fun uu____13008  ->
                                     match (uu____13007, uu____13008) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13109 =
                                           let uu____13116 =
                                             let uu____13119 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13119
                                              in
                                           copy_uvar u_lhs [] uu____13116 wl2
                                            in
                                         (match uu____13109 with
                                          | (uu____13148,t_a,wl3) ->
                                              let uu____13151 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13151 with
                                               | (uu____13170,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12945
                                ([], wl1)
                               in
                            (match uu____12932 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___372_13226 = ct  in
                                   let uu____13227 =
                                     let uu____13230 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13230
                                      in
                                   let uu____13245 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___372_13226.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___372_13226.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13227;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13245;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___372_13226.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___373_13263 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___373_13263.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___373_13263.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13266 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13266 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13328 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13328 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13339 =
                                          let uu____13344 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13344)  in
                                        TERM uu____13339  in
                                      let uu____13345 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13345 with
                                       | (sub_prob,wl3) ->
                                           let uu____13358 =
                                             let uu____13359 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13359
                                              in
                                           solve env uu____13358))
                             | (x,imp)::formals2 ->
                                 let uu____13381 =
                                   let uu____13388 =
                                     let uu____13391 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13391
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13388 wl1
                                    in
                                 (match uu____13381 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13412 =
                                          let uu____13415 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13415
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13412 u_x
                                         in
                                      let uu____13416 =
                                        let uu____13419 =
                                          let uu____13422 =
                                            let uu____13423 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13423, imp)  in
                                          [uu____13422]  in
                                        FStar_List.append bs_terms
                                          uu____13419
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13416 formals2 wl2)
                              in
                           let uu____13450 = occurs_check u_lhs arrow1  in
                           (match uu____13450 with
                            | (uu____13461,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13472 =
                                    let uu____13473 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13473
                                     in
                                  giveup_or_defer env orig wl uu____13472
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
              (let uu____13502 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13502
               then
                 let uu____13503 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13504 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13503 (rel_to_string (p_rel orig)) uu____13504
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13625 = rhs wl1 scope env1 subst1  in
                     (match uu____13625 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13645 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13645
                            then
                              let uu____13646 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13646
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____13719 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____13719 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___374_13721 = hd1  in
                       let uu____13722 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___374_13721.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___374_13721.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13722
                       }  in
                     let hd21 =
                       let uu___375_13726 = hd2  in
                       let uu____13727 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___375_13726.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___375_13726.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13727
                       }  in
                     let uu____13730 =
                       let uu____13735 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13735
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13730 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13754 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13754
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13758 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13758 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13821 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13821
                                  in
                               ((let uu____13839 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13839
                                 then
                                   let uu____13840 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13841 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13840
                                     uu____13841
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13868 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13901 = aux wl [] env [] bs1 bs2  in
               match uu____13901 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13950 = attempt sub_probs wl2  in
                   solve env uu____13950)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13955 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13955 wl)

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
              let uu____13969 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13969 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____14003 = lhs1  in
              match uu____14003 with
              | (uu____14006,ctx_u,uu____14008) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____14016 ->
                        let uu____14017 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____14017 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____14064 = quasi_pattern env1 lhs1  in
              match uu____14064 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____14094) ->
                  let uu____14099 = lhs1  in
                  (match uu____14099 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____14113 = occurs_check ctx_u rhs1  in
                       (match uu____14113 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14155 =
                                let uu____14162 =
                                  let uu____14163 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14163
                                   in
                                FStar_Util.Inl uu____14162  in
                              (uu____14155, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14185 =
                                 let uu____14186 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14186  in
                               if uu____14185
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14206 =
                                    let uu____14213 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14213  in
                                  let uu____14218 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14206, uu____14218)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14286  ->
                     match uu____14286 with
                     | (x,i) ->
                         let uu____14305 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14305, i)) bs_lhs
                 in
              let uu____14308 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14308 with
              | (rhs_hd,args) ->
                  let uu____14351 = FStar_Util.prefix args  in
                  (match uu____14351 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14423 = lhs1  in
                       (match uu____14423 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14427 =
                              let uu____14438 =
                                let uu____14445 =
                                  let uu____14448 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14448
                                   in
                                copy_uvar u_lhs [] uu____14445 wl1  in
                              match uu____14438 with
                              | (uu____14475,t_last_arg,wl2) ->
                                  let uu____14478 =
                                    let uu____14485 =
                                      let uu____14486 =
                                        let uu____14495 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14495]  in
                                      FStar_List.append bs_lhs uu____14486
                                       in
                                    copy_uvar u_lhs uu____14485 t_res_lhs wl2
                                     in
                                  (match uu____14478 with
                                   | (uu____14530,lhs',wl3) ->
                                       let uu____14533 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14533 with
                                        | (uu____14550,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14427 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14571 =
                                     let uu____14572 =
                                       let uu____14577 =
                                         let uu____14578 =
                                           let uu____14581 =
                                             let uu____14586 =
                                               let uu____14587 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14587]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14586
                                              in
                                           uu____14581
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14578
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14577)  in
                                     TERM uu____14572  in
                                   [uu____14571]  in
                                 let uu____14614 =
                                   let uu____14621 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14621 with
                                   | (p1,wl3) ->
                                       let uu____14640 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14640 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14614 with
                                  | (sub_probs,wl3) ->
                                      let uu____14671 =
                                        let uu____14672 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14672  in
                                      solve env1 uu____14671))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14705 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14705 with
                | (uu____14722,args) ->
                    (match args with | [] -> false | uu____14756 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14773 =
                  let uu____14774 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14774.FStar_Syntax_Syntax.n  in
                match uu____14773 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14777 -> true
                | uu____14792 -> false  in
              let uu____14793 = quasi_pattern env1 lhs1  in
              match uu____14793 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14804 =
                    let uu____14805 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14805
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14804
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14812 = is_app rhs1  in
                  if uu____14812
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14814 = is_arrow rhs1  in
                     if uu____14814
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14816 =
                          let uu____14817 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14817
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14816))
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
                let uu____14820 = lhs  in
                (match uu____14820 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14824 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14824 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14841 =
                              let uu____14844 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14844
                               in
                            FStar_All.pipe_right uu____14841
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14861 = occurs_check ctx_uv rhs1  in
                          (match uu____14861 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14883 =
                                   let uu____14884 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14884
                                    in
                                 giveup_or_defer env orig wl uu____14883
                               else
                                 (let uu____14886 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14886
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14891 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14891
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14893 =
                                         let uu____14894 =
                                           names_to_string1 fvs2  in
                                         let uu____14895 =
                                           names_to_string1 fvs1  in
                                         let uu____14896 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14894 uu____14895
                                           uu____14896
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14893)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14904 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14908 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14908 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14931 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14931
                             | (FStar_Util.Inl msg,uu____14933) ->
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
                  (let uu____14966 =
                     let uu____14983 = quasi_pattern env lhs  in
                     let uu____14990 = quasi_pattern env rhs  in
                     (uu____14983, uu____14990)  in
                   match uu____14966 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____15033 = lhs  in
                       (match uu____15033 with
                        | ({ FStar_Syntax_Syntax.n = uu____15034;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____15036;_},u_lhs,uu____15038)
                            ->
                            let uu____15041 = rhs  in
                            (match uu____15041 with
                             | (uu____15042,u_rhs,uu____15044) ->
                                 let uu____15045 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____15045
                                 then
                                   let uu____15050 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____15050
                                 else
                                   (let uu____15052 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____15052 with
                                    | (sub_prob,wl1) ->
                                        let uu____15065 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____15065 with
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
                                             let uu____15097 =
                                               let uu____15104 =
                                                 let uu____15107 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____15107
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
                                                 uu____15104
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____15097 with
                                              | (uu____15110,w,wl2) ->
                                                  let w_app =
                                                    let uu____15116 =
                                                      let uu____15121 =
                                                        FStar_List.map
                                                          (fun uu____15132 
                                                             ->
                                                             match uu____15132
                                                             with
                                                             | (z,uu____15140)
                                                                 ->
                                                                 let uu____15145
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____15145)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____15121
                                                       in
                                                    uu____15116
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____15149 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____15149
                                                    then
                                                      let uu____15150 =
                                                        let uu____15153 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____15154 =
                                                          let uu____15157 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____15158 =
                                                            let uu____15161 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____15162 =
                                                              let uu____15165
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____15172
                                                                =
                                                                let uu____15175
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____15182
                                                                  =
                                                                  let uu____15185
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____15185]
                                                                   in
                                                                uu____15175
                                                                  ::
                                                                  uu____15182
                                                                 in
                                                              uu____15165 ::
                                                                uu____15172
                                                               in
                                                            uu____15161 ::
                                                              uu____15162
                                                             in
                                                          uu____15157 ::
                                                            uu____15158
                                                           in
                                                        uu____15153 ::
                                                          uu____15154
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____15150
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____15191 =
                                                          let uu____15196 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____15196)
                                                           in
                                                        TERM uu____15191  in
                                                      let uu____15197 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____15197
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____15202 =
                                                             let uu____15207
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
                                                               uu____15207)
                                                              in
                                                           TERM uu____15202
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____15208 =
                                                      let uu____15209 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____15209
                                                       in
                                                    solve env uu____15208)))))))
                   | uu____15210 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____15274 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15274
            then
              let uu____15275 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15276 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15277 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15278 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15275 uu____15276 uu____15277 uu____15278
            else ());
           (let uu____15281 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15281 with
            | (head1,args1) ->
                let uu____15324 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15324 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15388 =
                         let uu____15389 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15390 = args_to_string args1  in
                         let uu____15393 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15394 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15389 uu____15390 uu____15393 uu____15394
                          in
                       giveup env1 uu____15388 orig
                     else
                       (let uu____15398 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15404 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15404 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15398
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___376_15406 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___376_15406.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___376_15406.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___376_15406.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___376_15406.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___376_15406.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___376_15406.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___376_15406.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___376_15406.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____15408 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____15408 with
                              | USolved wl2 ->
                                  let uu____15410 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____15410
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____15414 = base_and_refinement env1 t1  in
                           match uu____15414 with
                           | (base1,refinement1) ->
                               let uu____15439 = base_and_refinement env1 t2
                                  in
                               (match uu____15439 with
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
                                           let uu____15559 =
                                             FStar_List.fold_right
                                               (fun uu____15599  ->
                                                  fun uu____15600  ->
                                                    match (uu____15599,
                                                            uu____15600)
                                                    with
                                                    | (((a1,uu____15652),
                                                        (a2,uu____15654)),
                                                       (probs,wl2)) ->
                                                        let uu____15703 =
                                                          let uu____15710 =
                                                            p_scope orig  in
                                                          mk_problem wl2
                                                            uu____15710 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15703
                                                         with
                                                         | (prob',wl3) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl3)))
                                               argp ([], wl1)
                                              in
                                           (match uu____15559 with
                                            | (subprobs,wl2) ->
                                                ((let uu____15742 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____15742
                                                  then
                                                    let uu____15743 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____15743
                                                  else ());
                                                 (let formula =
                                                    let uu____15748 =
                                                      FStar_List.map
                                                        (fun p  -> p_guard p)
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____15748
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  let uu____15756 =
                                                    attempt subprobs wl3  in
                                                  solve env1 uu____15756)))
                                         else
                                           (let uu____15758 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____15758 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let uu____15762 =
                                                  FStar_List.fold_right2
                                                    (fun uu____15799  ->
                                                       fun uu____15800  ->
                                                         fun uu____15801  ->
                                                           match (uu____15799,
                                                                   uu____15800,
                                                                   uu____15801)
                                                           with
                                                           | ((a,uu____15845),
                                                              (a',uu____15847),
                                                              (subprobs,wl3))
                                                               ->
                                                               let uu____15880
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 []
                                                                   orig a
                                                                   FStar_TypeChecker_Common.EQ
                                                                   a'
                                                                   FStar_Pervasives_Native.None
                                                                   "index"
                                                                  in
                                                               (match uu____15880
                                                                with
                                                                | (p,wl4) ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                    args1 args2 ([], wl2)
                                                   in
                                                (match uu____15762 with
                                                 | (subprobs,wl3) ->
                                                     ((let uu____15910 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           (FStar_Options.Other
                                                              "Rel")
                                                          in
                                                       if uu____15910
                                                       then
                                                         let uu____15911 =
                                                           FStar_Syntax_Print.list_to_string
                                                             (prob_to_string
                                                                env1)
                                                             subprobs
                                                            in
                                                         FStar_Util.print1
                                                           "Adding subproblems for arguments: %s\n"
                                                           uu____15911
                                                       else ());
                                                      FStar_List.iter
                                                        (def_check_prob
                                                           "solve_t' subprobs")
                                                        subprobs;
                                                      (let formula =
                                                         let uu____15917 =
                                                           FStar_List.map
                                                             p_guard subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____15917
                                                          in
                                                       let wl4 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl3
                                                          in
                                                       let uu____15925 =
                                                         attempt subprobs wl4
                                                          in
                                                       solve env1 uu____15925))))
                                     | uu____15926 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___377_15962 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___377_15962.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___377_15962.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___377_15962.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___377_15962.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___377_15962.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___377_15962.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___377_15962.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___377_15962.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16037 = destruct_flex_t scrutinee wl1  in
             match uu____16037 with
             | ((_t,uv,_args),wl2) ->
                 let tc_annot env2 t =
                   let uu____16063 =
                     env2.FStar_TypeChecker_Env.type_of
                       (let uu___378_16071 = env2  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___378_16071.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___378_16071.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___378_16071.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___378_16071.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___378_16071.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___378_16071.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___378_16071.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___378_16071.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___378_16071.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___378_16071.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___378_16071.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___378_16071.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___378_16071.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___378_16071.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___378_16071.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___378_16071.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___378_16071.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___378_16071.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___378_16071.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___378_16071.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___378_16071.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___378_16071.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___378_16071.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___378_16071.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___378_16071.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___378_16071.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___378_16071.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___378_16071.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___378_16071.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts = true;
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___378_16071.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___378_16071.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___378_16071.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___378_16071.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___378_16071.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___378_16071.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___378_16071.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___378_16071.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___378_16071.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___378_16071.FStar_TypeChecker_Env.dep_graph);
                          FStar_TypeChecker_Env.nbe =
                            (uu___378_16071.FStar_TypeChecker_Env.nbe)
                        }) t
                      in
                   match uu____16063 with | (t1,uu____16077,g) -> (t1, g)  in
                 let uu____16079 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p
                     tc_annot
                    in
                 (match uu____16079 with
                  | (xs,pat_term,uu____16094,uu____16095) ->
                      let uu____16100 =
                        FStar_List.fold_left
                          (fun uu____16123  ->
                             fun x  ->
                               match uu____16123 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____16144 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____16144 with
                                    | (uu____16163,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____16100 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____16184 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____16184 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___379_16200 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___379_16200.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    tcenv = (uu___379_16200.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____16208 = solve env1 wl'  in
                                (match uu____16208 with
                                 | Success (uu____16211,imps) ->
                                     let wl'1 =
                                       let uu___380_16214 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___380_16214.wl_deferred);
                                         ctr = (uu___380_16214.ctr);
                                         defer_ok = (uu___380_16214.defer_ok);
                                         smt_ok = (uu___380_16214.smt_ok);
                                         tcenv = (uu___380_16214.tcenv);
                                         wl_implicits =
                                           (uu___380_16214.wl_implicits)
                                       }  in
                                     let uu____16215 = solve env1 wl'1  in
                                     (match uu____16215 with
                                      | Success (uu____16218,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___381_16222 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___381_16222.attempting);
                                                 wl_deferred =
                                                   (uu___381_16222.wl_deferred);
                                                 ctr = (uu___381_16222.ctr);
                                                 defer_ok =
                                                   (uu___381_16222.defer_ok);
                                                 smt_ok =
                                                   (uu___381_16222.smt_ok);
                                                 tcenv =
                                                   (uu___381_16222.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16223 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16229 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16250 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16250
                 then
                   let uu____16251 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16252 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16251 uu____16252
                 else ());
                (let uu____16254 =
                   let uu____16275 =
                     let uu____16284 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16284)  in
                   let uu____16291 =
                     let uu____16300 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16300)  in
                   (uu____16275, uu____16291)  in
                 match uu____16254 with
                 | ((uu____16329,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16332;
                                   FStar_Syntax_Syntax.vars = uu____16333;_}),
                    (s,t)) ->
                     let uu____16404 =
                       let uu____16405 = is_flex scrutinee  in
                       Prims.op_Negation uu____16405  in
                     if uu____16404
                     then
                       ((let uu____16413 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16413
                         then
                           let uu____16414 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16414
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16426 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16426
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16432 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16432
                           then
                             let uu____16433 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16434 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16433 uu____16434
                           else ());
                          (let pat_discriminates uu___340_16455 =
                             match uu___340_16455 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16470;
                                  FStar_Syntax_Syntax.p = uu____16471;_},FStar_Pervasives_Native.None
                                ,uu____16472) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16485;
                                  FStar_Syntax_Syntax.p = uu____16486;_},FStar_Pervasives_Native.None
                                ,uu____16487) -> true
                             | uu____16512 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16612 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16612 with
                                       | (uu____16613,uu____16614,t') ->
                                           let uu____16632 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____16632 with
                                            | (FullMatch ,uu____16643) ->
                                                true
                                            | (HeadMatch
                                               uu____16656,uu____16657) ->
                                                true
                                            | uu____16670 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16703 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16703
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16708 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16708 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16796,uu____16797) ->
                                       branches1
                                   | uu____16942 -> branches  in
                                 let uu____16997 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17006 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17006 with
                                        | (p,uu____17010,uu____17011) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____16997))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17067 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17067 with
                                | (p,uu____17075,e) ->
                                    ((let uu____17094 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17094
                                      then
                                        let uu____17095 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17096 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17095 uu____17096
                                      else ());
                                     (let uu____17098 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____17098)))))
                 | ((s,t),(uu____17113,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____17116;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17117;_}))
                     ->
                     let uu____17186 =
                       let uu____17187 = is_flex scrutinee  in
                       Prims.op_Negation uu____17187  in
                     if uu____17186
                     then
                       ((let uu____17195 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____17195
                         then
                           let uu____17196 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17196
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17208 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17208
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17214 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17214
                           then
                             let uu____17215 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____17216 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17215 uu____17216
                           else ());
                          (let pat_discriminates uu___340_17237 =
                             match uu___340_17237 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17252;
                                  FStar_Syntax_Syntax.p = uu____17253;_},FStar_Pervasives_Native.None
                                ,uu____17254) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17267;
                                  FStar_Syntax_Syntax.p = uu____17268;_},FStar_Pervasives_Native.None
                                ,uu____17269) -> true
                             | uu____17294 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17394 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17394 with
                                       | (uu____17395,uu____17396,t') ->
                                           let uu____17414 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____17414 with
                                            | (FullMatch ,uu____17425) ->
                                                true
                                            | (HeadMatch
                                               uu____17438,uu____17439) ->
                                                true
                                            | uu____17452 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17485 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17485
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17490 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17490 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17578,uu____17579) ->
                                       branches1
                                   | uu____17724 -> branches  in
                                 let uu____17779 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17788 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17788 with
                                        | (p,uu____17792,uu____17793) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17779))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17849 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17849 with
                                | (p,uu____17857,e) ->
                                    ((let uu____17876 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17876
                                      then
                                        let uu____17877 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17878 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17877 uu____17878
                                      else ());
                                     (let uu____17880 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17880)))))
                 | uu____17893 ->
                     ((let uu____17915 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17915
                       then
                         let uu____17916 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17917 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17916 uu____17917
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____17958 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____17958
            then
              let uu____17959 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17960 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____17961 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17962 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____17959 uu____17960 uu____17961 uu____17962
            else ());
           (let uu____17964 = head_matches_delta env1 t1 t2  in
            match uu____17964 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____17995,uu____17996) ->
                     let rec may_relate head3 =
                       let uu____18023 =
                         let uu____18024 = FStar_Syntax_Subst.compress head3
                            in
                         uu____18024.FStar_Syntax_Syntax.n  in
                       match uu____18023 with
                       | FStar_Syntax_Syntax.Tm_name uu____18027 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18028 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18051;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____18052;
                             FStar_Syntax_Syntax.fv_qual = uu____18053;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18056;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____18057;
                             FStar_Syntax_Syntax.fv_qual = uu____18058;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____18062,uu____18063) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____18105) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____18111) ->
                           may_relate t
                       | uu____18116 -> false  in
                     let uu____18117 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____18117 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____18132 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____18132
                          then
                            let uu____18133 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____18133 with
                             | (guard,wl2) ->
                                 let uu____18140 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____18140)
                          else
                            (let uu____18142 =
                               let uu____18143 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____18144 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               FStar_Util.format2 "head mismatch (%s vs %s)"
                                 uu____18143 uu____18144
                                in
                             giveup env1 uu____18142 orig))
                 | (HeadMatch (true ),uu____18145) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18158 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____18158 with
                        | (guard,wl2) ->
                            let uu____18165 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____18165)
                     else
                       (let uu____18167 =
                          let uu____18168 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____18169 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____18168 uu____18169
                           in
                        giveup env1 uu____18167 orig)
                 | (uu____18170,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___382_18184 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___382_18184.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___382_18184.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___382_18184.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___382_18184.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___382_18184.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___382_18184.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___382_18184.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___382_18184.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18208 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18208
          then
            let uu____18209 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18209
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18214 =
                let uu____18217 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18217  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18214 t1);
             (let uu____18235 =
                let uu____18238 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18238  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18235 t2);
             (let uu____18256 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18256
              then
                let uu____18257 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18258 =
                  let uu____18259 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18260 =
                    let uu____18261 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18261  in
                  Prims.strcat uu____18259 uu____18260  in
                let uu____18262 =
                  let uu____18263 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18264 =
                    let uu____18265 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18265  in
                  Prims.strcat uu____18263 uu____18264  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18257
                  uu____18258 uu____18262
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18268,uu____18269) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18292,FStar_Syntax_Syntax.Tm_delayed uu____18293) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18316,uu____18317) ->
                  let uu____18344 =
                    let uu___383_18345 = problem  in
                    let uu____18346 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___383_18345.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18346;
                      FStar_TypeChecker_Common.relation =
                        (uu___383_18345.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___383_18345.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___383_18345.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___383_18345.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___383_18345.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___383_18345.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___383_18345.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___383_18345.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18344 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18347,uu____18348) ->
                  let uu____18355 =
                    let uu___384_18356 = problem  in
                    let uu____18357 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___384_18356.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18357;
                      FStar_TypeChecker_Common.relation =
                        (uu___384_18356.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___384_18356.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___384_18356.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___384_18356.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___384_18356.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___384_18356.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___384_18356.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___384_18356.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18355 wl
              | (uu____18358,FStar_Syntax_Syntax.Tm_ascribed uu____18359) ->
                  let uu____18386 =
                    let uu___385_18387 = problem  in
                    let uu____18388 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___385_18387.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___385_18387.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___385_18387.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18388;
                      FStar_TypeChecker_Common.element =
                        (uu___385_18387.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___385_18387.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___385_18387.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___385_18387.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___385_18387.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___385_18387.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18386 wl
              | (uu____18389,FStar_Syntax_Syntax.Tm_meta uu____18390) ->
                  let uu____18397 =
                    let uu___386_18398 = problem  in
                    let uu____18399 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___386_18398.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___386_18398.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___386_18398.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18399;
                      FStar_TypeChecker_Common.element =
                        (uu___386_18398.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___386_18398.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___386_18398.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___386_18398.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___386_18398.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___386_18398.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18397 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18401),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18403)) ->
                  let uu____18412 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18412
              | (FStar_Syntax_Syntax.Tm_bvar uu____18413,uu____18414) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18415,FStar_Syntax_Syntax.Tm_bvar uu____18416) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___341_18485 =
                    match uu___341_18485 with
                    | [] -> c
                    | bs ->
                        let uu____18513 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18513
                     in
                  let uu____18524 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18524 with
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
                                    let uu____18673 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18673
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
                  let mk_t t l uu___342_18758 =
                    match uu___342_18758 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18800 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18800 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____18945 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____18946 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____18945
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____18946 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____18947,uu____18948) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18977 -> true
                    | uu____18996 -> false  in
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
                      (let uu____19049 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_19057 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_19057.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_19057.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_19057.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_19057.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_19057.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_19057.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_19057.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_19057.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_19057.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_19057.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_19057.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_19057.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_19057.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_19057.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_19057.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_19057.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_19057.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_19057.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_19057.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_19057.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_19057.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_19057.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_19057.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_19057.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_19057.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_19057.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_19057.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_19057.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_19057.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_19057.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_19057.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_19057.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_19057.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_19057.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_19057.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_19057.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_19057.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___387_19057.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_19057.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19049 with
                       | (uu____19060,ty,uu____19062) ->
                           let uu____19063 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19063)
                     in
                  let uu____19064 =
                    let uu____19081 = maybe_eta t1  in
                    let uu____19088 = maybe_eta t2  in
                    (uu____19081, uu____19088)  in
                  (match uu____19064 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_19130 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_19130.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_19130.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_19130.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_19130.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_19130.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_19130.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_19130.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_19130.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19151 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19151
                       then
                         let uu____19152 = destruct_flex_t not_abs wl  in
                         (match uu____19152 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19167 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19167.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19167.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19167.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19167.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19167.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19167.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19167.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19167.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19189 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19189
                       then
                         let uu____19190 = destruct_flex_t not_abs wl  in
                         (match uu____19190 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19205 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19205.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19205.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19205.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19205.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19205.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19205.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19205.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19205.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19207 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19224,FStar_Syntax_Syntax.Tm_abs uu____19225) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19254 -> true
                    | uu____19273 -> false  in
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
                      (let uu____19326 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_19334 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_19334.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_19334.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_19334.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_19334.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_19334.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_19334.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_19334.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_19334.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_19334.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_19334.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_19334.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_19334.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_19334.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_19334.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_19334.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_19334.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_19334.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_19334.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_19334.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_19334.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_19334.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_19334.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_19334.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_19334.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_19334.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_19334.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_19334.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_19334.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_19334.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_19334.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_19334.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_19334.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_19334.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_19334.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_19334.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_19334.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_19334.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___387_19334.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_19334.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19326 with
                       | (uu____19337,ty,uu____19339) ->
                           let uu____19340 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19340)
                     in
                  let uu____19341 =
                    let uu____19358 = maybe_eta t1  in
                    let uu____19365 = maybe_eta t2  in
                    (uu____19358, uu____19365)  in
                  (match uu____19341 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_19407 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_19407.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_19407.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_19407.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_19407.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_19407.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_19407.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_19407.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_19407.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19428 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19428
                       then
                         let uu____19429 = destruct_flex_t not_abs wl  in
                         (match uu____19429 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19444 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19444.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19444.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19444.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19444.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19444.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19444.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19444.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19444.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19466 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19466
                       then
                         let uu____19467 = destruct_flex_t not_abs wl  in
                         (match uu____19467 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19482 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19482.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19482.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19482.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19482.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19482.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19482.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19482.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19482.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19484 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19513 =
                    let uu____19518 =
                      head_matches_delta env x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19518 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___390_19546 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19546.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19546.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19548 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19548.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19548.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19549,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___390_19563 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19563.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19563.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19565 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19565.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19565.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19566 -> (x1, x2)  in
                  (match uu____19513 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19585 = as_refinement false env t11  in
                       (match uu____19585 with
                        | (x12,phi11) ->
                            let uu____19592 = as_refinement false env t21  in
                            (match uu____19592 with
                             | (x22,phi21) ->
                                 ((let uu____19600 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19600
                                   then
                                     ((let uu____19602 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19603 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19604 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19602
                                         uu____19603 uu____19604);
                                      (let uu____19605 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19606 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19607 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19605
                                         uu____19606 uu____19607))
                                   else ());
                                  (let uu____19609 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19609 with
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
                                         let uu____19677 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19677
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19689 =
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
                                         (let uu____19700 =
                                            let uu____19703 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19703
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19700
                                            (p_guard base_prob));
                                         (let uu____19721 =
                                            let uu____19724 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19724
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19721
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19742 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19742)
                                          in
                                       let has_uvars =
                                         (let uu____19746 =
                                            let uu____19747 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19747
                                             in
                                          Prims.op_Negation uu____19746) ||
                                           (let uu____19751 =
                                              let uu____19752 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19752
                                               in
                                            Prims.op_Negation uu____19751)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19755 =
                                           let uu____19760 =
                                             let uu____19769 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19769]  in
                                           mk_t_problem wl1 uu____19760 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19755 with
                                          | (ref_prob,wl2) ->
                                              let uu____19790 =
                                                solve env1
                                                  (let uu___392_19792 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___392_19792.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___392_19792.smt_ok);
                                                     tcenv =
                                                       (uu___392_19792.tcenv);
                                                     wl_implicits =
                                                       (uu___392_19792.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19790 with
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
                                               | Success uu____19802 ->
                                                   let guard =
                                                     let uu____19810 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19810
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___393_19819 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___393_19819.attempting);
                                                       wl_deferred =
                                                         (uu___393_19819.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___393_19819.defer_ok);
                                                       smt_ok =
                                                         (uu___393_19819.smt_ok);
                                                       tcenv =
                                                         (uu___393_19819.tcenv);
                                                       wl_implicits =
                                                         (uu___393_19819.wl_implicits)
                                                     }  in
                                                   let uu____19820 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19820))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19822,FStar_Syntax_Syntax.Tm_uvar uu____19823) ->
                  let uu____19848 = destruct_flex_t t1 wl  in
                  (match uu____19848 with
                   | (f1,wl1) ->
                       let uu____19855 = destruct_flex_t t2 wl1  in
                       (match uu____19855 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19862;
                    FStar_Syntax_Syntax.pos = uu____19863;
                    FStar_Syntax_Syntax.vars = uu____19864;_},uu____19865),FStar_Syntax_Syntax.Tm_uvar
                 uu____19866) ->
                  let uu____19915 = destruct_flex_t t1 wl  in
                  (match uu____19915 with
                   | (f1,wl1) ->
                       let uu____19922 = destruct_flex_t t2 wl1  in
                       (match uu____19922 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19929,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19930;
                    FStar_Syntax_Syntax.pos = uu____19931;
                    FStar_Syntax_Syntax.vars = uu____19932;_},uu____19933))
                  ->
                  let uu____19982 = destruct_flex_t t1 wl  in
                  (match uu____19982 with
                   | (f1,wl1) ->
                       let uu____19989 = destruct_flex_t t2 wl1  in
                       (match uu____19989 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19996;
                    FStar_Syntax_Syntax.pos = uu____19997;
                    FStar_Syntax_Syntax.vars = uu____19998;_},uu____19999),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20000;
                    FStar_Syntax_Syntax.pos = uu____20001;
                    FStar_Syntax_Syntax.vars = uu____20002;_},uu____20003))
                  ->
                  let uu____20076 = destruct_flex_t t1 wl  in
                  (match uu____20076 with
                   | (f1,wl1) ->
                       let uu____20083 = destruct_flex_t t2 wl1  in
                       (match uu____20083 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20090,uu____20091) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20104 = destruct_flex_t t1 wl  in
                  (match uu____20104 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20111;
                    FStar_Syntax_Syntax.pos = uu____20112;
                    FStar_Syntax_Syntax.vars = uu____20113;_},uu____20114),uu____20115)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20152 = destruct_flex_t t1 wl  in
                  (match uu____20152 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____20159,FStar_Syntax_Syntax.Tm_uvar uu____20160) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____20173,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20174;
                    FStar_Syntax_Syntax.pos = uu____20175;
                    FStar_Syntax_Syntax.vars = uu____20176;_},uu____20177))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20214,FStar_Syntax_Syntax.Tm_arrow uu____20215) ->
                  solve_t' env
                    (let uu___394_20243 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20243.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20243.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20243.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20243.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20243.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20243.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20243.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20243.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20243.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20244;
                    FStar_Syntax_Syntax.pos = uu____20245;
                    FStar_Syntax_Syntax.vars = uu____20246;_},uu____20247),FStar_Syntax_Syntax.Tm_arrow
                 uu____20248) ->
                  solve_t' env
                    (let uu___394_20300 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20300.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20300.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20300.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20300.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20300.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20300.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20300.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20300.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20300.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20301,FStar_Syntax_Syntax.Tm_uvar uu____20302) ->
                  let uu____20315 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20315
              | (uu____20316,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20317;
                    FStar_Syntax_Syntax.pos = uu____20318;
                    FStar_Syntax_Syntax.vars = uu____20319;_},uu____20320))
                  ->
                  let uu____20357 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20357
              | (FStar_Syntax_Syntax.Tm_uvar uu____20358,uu____20359) ->
                  let uu____20372 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20372
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20373;
                    FStar_Syntax_Syntax.pos = uu____20374;
                    FStar_Syntax_Syntax.vars = uu____20375;_},uu____20376),uu____20377)
                  ->
                  let uu____20414 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20414
              | (FStar_Syntax_Syntax.Tm_refine uu____20415,uu____20416) ->
                  let t21 =
                    let uu____20424 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20424  in
                  solve_t env
                    (let uu___395_20450 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___395_20450.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___395_20450.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___395_20450.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___395_20450.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___395_20450.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___395_20450.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___395_20450.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___395_20450.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___395_20450.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20451,FStar_Syntax_Syntax.Tm_refine uu____20452) ->
                  let t11 =
                    let uu____20460 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20460  in
                  solve_t env
                    (let uu___396_20486 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___396_20486.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___396_20486.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___396_20486.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___396_20486.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___396_20486.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___396_20486.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___396_20486.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___396_20486.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___396_20486.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20568 =
                    let uu____20569 = guard_of_prob env wl problem t1 t2  in
                    match uu____20569 with
                    | (guard,wl1) ->
                        let uu____20576 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20576
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20787 = br1  in
                        (match uu____20787 with
                         | (p1,w1,uu____20812) ->
                             let uu____20829 = br2  in
                             (match uu____20829 with
                              | (p2,w2,uu____20848) ->
                                  let uu____20853 =
                                    let uu____20854 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20854  in
                                  if uu____20853
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20870 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20870 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____20903 = br2  in
                                         (match uu____20903 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____20940 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____20940
                                                 in
                                              let uu____20953 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____20976,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____20993) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____21036 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____21036 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____20953
                                                (fun uu____21078  ->
                                                   match uu____21078 with
                                                   | (wprobs,wl2) ->
                                                       let uu____21099 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____21099
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____21114 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____21114
                                                              (fun
                                                                 uu____21138 
                                                                 ->
                                                                 match uu____21138
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____21223 -> FStar_Pervasives_Native.None  in
                  let uu____21260 = solve_branches wl brs1 brs2  in
                  (match uu____21260 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21288 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21288 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____21307 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21307  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21316 =
                              let uu____21317 =
                                attempt sub_probs1
                                  (let uu___397_21319 = wl3  in
                                   {
                                     attempting = (uu___397_21319.attempting);
                                     wl_deferred =
                                       (uu___397_21319.wl_deferred);
                                     ctr = (uu___397_21319.ctr);
                                     defer_ok = (uu___397_21319.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___397_21319.tcenv);
                                     wl_implicits =
                                       (uu___397_21319.wl_implicits)
                                   })
                                 in
                              solve env uu____21317  in
                            (match uu____21316 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21323 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21329,uu____21330) ->
                  let head1 =
                    let uu____21354 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21354
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21400 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21400
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21446 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21446
                    then
                      let uu____21447 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21448 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21449 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21447 uu____21448 uu____21449
                    else ());
                   (let no_free_uvars t =
                      (let uu____21459 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21459) &&
                        (let uu____21463 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21463)
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
                      let uu____21479 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21479 = FStar_Syntax_Util.Equal  in
                    let uu____21480 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21480
                    then
                      let uu____21481 =
                        let uu____21488 = equal t1 t2  in
                        if uu____21488
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21498 = mk_eq2 wl orig t1 t2  in
                           match uu____21498 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21481 with
                      | (guard,wl1) ->
                          let uu____21519 = solve_prob orig guard [] wl1  in
                          solve env uu____21519
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21521,uu____21522) ->
                  let head1 =
                    let uu____21530 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21530
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21576 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21576
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21622 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21622
                    then
                      let uu____21623 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21624 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21625 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21623 uu____21624 uu____21625
                    else ());
                   (let no_free_uvars t =
                      (let uu____21635 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21635) &&
                        (let uu____21639 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21639)
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
                      let uu____21655 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21655 = FStar_Syntax_Util.Equal  in
                    let uu____21656 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21656
                    then
                      let uu____21657 =
                        let uu____21664 = equal t1 t2  in
                        if uu____21664
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21674 = mk_eq2 wl orig t1 t2  in
                           match uu____21674 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21657 with
                      | (guard,wl1) ->
                          let uu____21695 = solve_prob orig guard [] wl1  in
                          solve env uu____21695
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____21697,uu____21698) ->
                  let head1 =
                    let uu____21700 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21700
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21746 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21746
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21792 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21792
                    then
                      let uu____21793 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21794 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21795 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21793 uu____21794 uu____21795
                    else ());
                   (let no_free_uvars t =
                      (let uu____21805 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21805) &&
                        (let uu____21809 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21809)
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
                      let uu____21825 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21825 = FStar_Syntax_Util.Equal  in
                    let uu____21826 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21826
                    then
                      let uu____21827 =
                        let uu____21834 = equal t1 t2  in
                        if uu____21834
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21844 = mk_eq2 wl orig t1 t2  in
                           match uu____21844 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21827 with
                      | (guard,wl1) ->
                          let uu____21865 = solve_prob orig guard [] wl1  in
                          solve env uu____21865
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____21867,uu____21868) ->
                  let head1 =
                    let uu____21870 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21870
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21916 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21916
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21962 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21962
                    then
                      let uu____21963 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21964 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21965 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21963 uu____21964 uu____21965
                    else ());
                   (let no_free_uvars t =
                      (let uu____21975 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21975) &&
                        (let uu____21979 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21979)
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
                      let uu____21995 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21995 = FStar_Syntax_Util.Equal  in
                    let uu____21996 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21996
                    then
                      let uu____21997 =
                        let uu____22004 = equal t1 t2  in
                        if uu____22004
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22014 = mk_eq2 wl orig t1 t2  in
                           match uu____22014 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21997 with
                      | (guard,wl1) ->
                          let uu____22035 = solve_prob orig guard [] wl1  in
                          solve env uu____22035
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____22037,uu____22038) ->
                  let head1 =
                    let uu____22040 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22040
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22086 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22086
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22132 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22132
                    then
                      let uu____22133 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22134 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22135 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22133 uu____22134 uu____22135
                    else ());
                   (let no_free_uvars t =
                      (let uu____22145 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22145) &&
                        (let uu____22149 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22149)
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
                      let uu____22165 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22165 = FStar_Syntax_Util.Equal  in
                    let uu____22166 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22166
                    then
                      let uu____22167 =
                        let uu____22174 = equal t1 t2  in
                        if uu____22174
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22184 = mk_eq2 wl orig t1 t2  in
                           match uu____22184 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22167 with
                      | (guard,wl1) ->
                          let uu____22205 = solve_prob orig guard [] wl1  in
                          solve env uu____22205
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22207,uu____22208) ->
                  let head1 =
                    let uu____22226 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22226
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22272 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22272
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22318 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22318
                    then
                      let uu____22319 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22320 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22321 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22319 uu____22320 uu____22321
                    else ());
                   (let no_free_uvars t =
                      (let uu____22331 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22331) &&
                        (let uu____22335 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22335)
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
                      let uu____22351 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22351 = FStar_Syntax_Util.Equal  in
                    let uu____22352 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22352
                    then
                      let uu____22353 =
                        let uu____22360 = equal t1 t2  in
                        if uu____22360
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22370 = mk_eq2 wl orig t1 t2  in
                           match uu____22370 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22353 with
                      | (guard,wl1) ->
                          let uu____22391 = solve_prob orig guard [] wl1  in
                          solve env uu____22391
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22393,FStar_Syntax_Syntax.Tm_match uu____22394) ->
                  let head1 =
                    let uu____22418 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22418
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22464 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22464
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22510 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22510
                    then
                      let uu____22511 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22512 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22513 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22511 uu____22512 uu____22513
                    else ());
                   (let no_free_uvars t =
                      (let uu____22523 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22523) &&
                        (let uu____22527 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22527)
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
                      let uu____22543 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22543 = FStar_Syntax_Util.Equal  in
                    let uu____22544 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22544
                    then
                      let uu____22545 =
                        let uu____22552 = equal t1 t2  in
                        if uu____22552
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22562 = mk_eq2 wl orig t1 t2  in
                           match uu____22562 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22545 with
                      | (guard,wl1) ->
                          let uu____22583 = solve_prob orig guard [] wl1  in
                          solve env uu____22583
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22585,FStar_Syntax_Syntax.Tm_uinst uu____22586) ->
                  let head1 =
                    let uu____22594 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22594
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22634 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22634
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22674 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22674
                    then
                      let uu____22675 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22676 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22677 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22675 uu____22676 uu____22677
                    else ());
                   (let no_free_uvars t =
                      (let uu____22687 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22687) &&
                        (let uu____22691 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22691)
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
                      let uu____22707 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22707 = FStar_Syntax_Util.Equal  in
                    let uu____22708 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22708
                    then
                      let uu____22709 =
                        let uu____22716 = equal t1 t2  in
                        if uu____22716
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22726 = mk_eq2 wl orig t1 t2  in
                           match uu____22726 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22709 with
                      | (guard,wl1) ->
                          let uu____22747 = solve_prob orig guard [] wl1  in
                          solve env uu____22747
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22749,FStar_Syntax_Syntax.Tm_name uu____22750) ->
                  let head1 =
                    let uu____22752 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22752
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22792 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22792
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22832 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22832
                    then
                      let uu____22833 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22834 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22835 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22833 uu____22834 uu____22835
                    else ());
                   (let no_free_uvars t =
                      (let uu____22845 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22845) &&
                        (let uu____22849 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22849)
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
                      let uu____22865 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22865 = FStar_Syntax_Util.Equal  in
                    let uu____22866 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22866
                    then
                      let uu____22867 =
                        let uu____22874 = equal t1 t2  in
                        if uu____22874
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22884 = mk_eq2 wl orig t1 t2  in
                           match uu____22884 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22867 with
                      | (guard,wl1) ->
                          let uu____22905 = solve_prob orig guard [] wl1  in
                          solve env uu____22905
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22907,FStar_Syntax_Syntax.Tm_constant uu____22908) ->
                  let head1 =
                    let uu____22910 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22910
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22950 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22950
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22990 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22990
                    then
                      let uu____22991 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22992 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22993 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22991 uu____22992 uu____22993
                    else ());
                   (let no_free_uvars t =
                      (let uu____23003 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23003) &&
                        (let uu____23007 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23007)
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
                      let uu____23023 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23023 = FStar_Syntax_Util.Equal  in
                    let uu____23024 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23024
                    then
                      let uu____23025 =
                        let uu____23032 = equal t1 t2  in
                        if uu____23032
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23042 = mk_eq2 wl orig t1 t2  in
                           match uu____23042 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23025 with
                      | (guard,wl1) ->
                          let uu____23063 = solve_prob orig guard [] wl1  in
                          solve env uu____23063
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23065,FStar_Syntax_Syntax.Tm_fvar uu____23066) ->
                  let head1 =
                    let uu____23068 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23068
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23114 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23114
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23160 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23160
                    then
                      let uu____23161 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23162 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23163 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23161 uu____23162 uu____23163
                    else ());
                   (let no_free_uvars t =
                      (let uu____23173 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23173) &&
                        (let uu____23177 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23177)
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
                      let uu____23193 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23193 = FStar_Syntax_Util.Equal  in
                    let uu____23194 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23194
                    then
                      let uu____23195 =
                        let uu____23202 = equal t1 t2  in
                        if uu____23202
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23212 = mk_eq2 wl orig t1 t2  in
                           match uu____23212 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23195 with
                      | (guard,wl1) ->
                          let uu____23233 = solve_prob orig guard [] wl1  in
                          solve env uu____23233
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23235,FStar_Syntax_Syntax.Tm_app uu____23236) ->
                  let head1 =
                    let uu____23254 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23254
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23294 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23294
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23334 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23334
                    then
                      let uu____23335 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23336 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23337 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23335 uu____23336 uu____23337
                    else ());
                   (let no_free_uvars t =
                      (let uu____23347 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23347) &&
                        (let uu____23351 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23351)
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
                      let uu____23367 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23367 = FStar_Syntax_Util.Equal  in
                    let uu____23368 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23368
                    then
                      let uu____23369 =
                        let uu____23376 = equal t1 t2  in
                        if uu____23376
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23386 = mk_eq2 wl orig t1 t2  in
                           match uu____23386 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23369 with
                      | (guard,wl1) ->
                          let uu____23407 = solve_prob orig guard [] wl1  in
                          solve env uu____23407
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23409,FStar_Syntax_Syntax.Tm_let uu____23410) ->
                  let uu____23435 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23435
                  then
                    let uu____23436 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23436
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23438,uu____23439) ->
                  let uu____23452 =
                    let uu____23457 =
                      let uu____23458 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23459 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23460 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23461 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23458 uu____23459 uu____23460 uu____23461
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23457)
                     in
                  FStar_Errors.raise_error uu____23452
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23462,FStar_Syntax_Syntax.Tm_let uu____23463) ->
                  let uu____23476 =
                    let uu____23481 =
                      let uu____23482 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23483 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23484 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23485 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23482 uu____23483 uu____23484 uu____23485
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23481)
                     in
                  FStar_Errors.raise_error uu____23476
                    t1.FStar_Syntax_Syntax.pos
              | uu____23486 -> giveup env "head tag mismatch" orig))))

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
          (let uu____23547 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23547
           then
             let uu____23548 =
               let uu____23549 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23549  in
             let uu____23550 =
               let uu____23551 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23551  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23548 uu____23550
           else ());
          (let uu____23553 =
             let uu____23554 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23554  in
           if uu____23553
           then
             let uu____23555 =
               let uu____23556 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23557 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23556 uu____23557
                in
             giveup env uu____23555 orig
           else
             (let uu____23559 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23559 with
              | (ret_sub_prob,wl1) ->
                  let uu____23566 =
                    FStar_List.fold_right2
                      (fun uu____23603  ->
                         fun uu____23604  ->
                           fun uu____23605  ->
                             match (uu____23603, uu____23604, uu____23605)
                             with
                             | ((a1,uu____23649),(a2,uu____23651),(arg_sub_probs,wl2))
                                 ->
                                 let uu____23684 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____23684 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23566 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____23713 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____23713  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____23721 = attempt sub_probs wl3  in
                       solve env uu____23721)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23744 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23747)::[] -> wp1
              | uu____23772 ->
                  let uu____23783 =
                    let uu____23784 =
                      let uu____23785 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23785  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23784
                     in
                  failwith uu____23783
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23791 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23791]
              | x -> x  in
            let uu____23793 =
              let uu____23804 =
                let uu____23813 =
                  let uu____23814 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23814 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23813  in
              [uu____23804]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23793;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23831 = lift_c1 ()  in solve_eq uu____23831 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___343_23837  ->
                       match uu___343_23837 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23838 -> false))
                in
             let uu____23839 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23869)::uu____23870,(wp2,uu____23872)::uu____23873)
                   -> (wp1, wp2)
               | uu____23946 ->
                   let uu____23971 =
                     let uu____23976 =
                       let uu____23977 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23978 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23977 uu____23978
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23976)
                      in
                   FStar_Errors.raise_error uu____23971
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23839 with
             | (wpc1,wpc2) ->
                 let uu____23985 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23985
                 then
                   let uu____23988 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23988 wl
                 else
                   (let uu____23990 =
                      let uu____23997 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23997  in
                    match uu____23990 with
                    | (c2_decl,qualifiers) ->
                        let uu____24018 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____24018
                        then
                          let c1_repr =
                            let uu____24022 =
                              let uu____24023 =
                                let uu____24024 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____24024  in
                              let uu____24025 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24023 uu____24025
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24022
                             in
                          let c2_repr =
                            let uu____24027 =
                              let uu____24028 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____24029 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24028 uu____24029
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24027
                             in
                          let uu____24030 =
                            let uu____24035 =
                              let uu____24036 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____24037 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____24036 uu____24037
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____24035
                             in
                          (match uu____24030 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____24041 = attempt [prob] wl2  in
                               solve env uu____24041)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____24052 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24052
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____24055 =
                                     let uu____24062 =
                                       let uu____24063 =
                                         let uu____24080 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____24083 =
                                           let uu____24094 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____24103 =
                                             let uu____24114 =
                                               let uu____24123 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____24123
                                                in
                                             [uu____24114]  in
                                           uu____24094 :: uu____24103  in
                                         (uu____24080, uu____24083)  in
                                       FStar_Syntax_Syntax.Tm_app uu____24063
                                        in
                                     FStar_Syntax_Syntax.mk uu____24062  in
                                   uu____24055 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____24174 =
                                    let uu____24181 =
                                      let uu____24182 =
                                        let uu____24199 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____24202 =
                                          let uu____24213 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24222 =
                                            let uu____24233 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24242 =
                                              let uu____24253 =
                                                let uu____24262 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24262
                                                 in
                                              [uu____24253]  in
                                            uu____24233 :: uu____24242  in
                                          uu____24213 :: uu____24222  in
                                        (uu____24199, uu____24202)  in
                                      FStar_Syntax_Syntax.Tm_app uu____24182
                                       in
                                    FStar_Syntax_Syntax.mk uu____24181  in
                                  uu____24174 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24319 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24319
                            then
                              let uu____24320 =
                                let uu____24321 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24321
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24320
                            else ());
                           (let uu____24323 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24323 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24331 =
                                    let uu____24334 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24334
                                     in
                                  solve_prob orig uu____24331 [] wl1  in
                                let uu____24337 = attempt [base_prob] wl2  in
                                solve env uu____24337))))
           in
        let uu____24338 = FStar_Util.physical_equality c1 c2  in
        if uu____24338
        then
          let uu____24339 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24339
        else
          ((let uu____24342 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24342
            then
              let uu____24343 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24344 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24343
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24344
            else ());
           (let uu____24346 =
              let uu____24355 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24358 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24355, uu____24358)  in
            match uu____24346 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24376),FStar_Syntax_Syntax.Total
                    (t2,uu____24378)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24395 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24395 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24396,FStar_Syntax_Syntax.Total uu____24397) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24415),FStar_Syntax_Syntax.Total
                    (t2,uu____24417)) ->
                     let uu____24434 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24434 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24436),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24438)) ->
                     let uu____24455 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24455 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24457),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24459)) ->
                     let uu____24476 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24476 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24477,FStar_Syntax_Syntax.Comp uu____24478) ->
                     let uu____24487 =
                       let uu___398_24490 = problem  in
                       let uu____24493 =
                         let uu____24494 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24494
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24490.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24493;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24490.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24490.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24490.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24490.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24490.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24490.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24490.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24490.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24487 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24495,FStar_Syntax_Syntax.Comp uu____24496) ->
                     let uu____24505 =
                       let uu___398_24508 = problem  in
                       let uu____24511 =
                         let uu____24512 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24512
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24508.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24511;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24508.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24508.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24508.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24508.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24508.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24508.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24508.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24508.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24505 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24513,FStar_Syntax_Syntax.GTotal uu____24514) ->
                     let uu____24523 =
                       let uu___399_24526 = problem  in
                       let uu____24529 =
                         let uu____24530 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24530
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24526.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24526.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24526.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24529;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24526.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24526.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24526.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24526.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24526.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24526.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24523 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24531,FStar_Syntax_Syntax.Total uu____24532) ->
                     let uu____24541 =
                       let uu___399_24544 = problem  in
                       let uu____24547 =
                         let uu____24548 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24548
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24544.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24544.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24544.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24547;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24544.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24544.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24544.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24544.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24544.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24544.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24541 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24549,FStar_Syntax_Syntax.Comp uu____24550) ->
                     let uu____24551 =
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
                     if uu____24551
                     then
                       let uu____24552 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24552 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24556 =
                            let uu____24561 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24561
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24567 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24568 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24567, uu____24568))
                             in
                          match uu____24556 with
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
                           (let uu____24575 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24575
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24577 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24577 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24580 =
                                  let uu____24581 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24582 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24581 uu____24582
                                   in
                                giveup env uu____24580 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24589 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24589 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24630 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24630 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24648 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24676  ->
                match uu____24676 with
                | (u1,u2) ->
                    let uu____24683 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24684 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24683 uu____24684))
         in
      FStar_All.pipe_right uu____24648 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24711,[])) -> "{}"
      | uu____24736 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24759 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____24759
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24762 =
              FStar_List.map
                (fun uu____24772  ->
                   match uu____24772 with
                   | (uu____24777,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24762 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24782 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24782 imps
  
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
                  let uu____24835 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____24835
                  then
                    let uu____24836 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____24837 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24836
                      (rel_to_string rel) uu____24837
                  else "TOP"  in
                let uu____24839 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____24839 with
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
              let uu____24897 =
                let uu____24900 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____24900
                 in
              FStar_Syntax_Syntax.new_bv uu____24897 t1  in
            let uu____24903 =
              let uu____24908 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____24908
               in
            match uu____24903 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____24981 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____24981
              then
                let uu____24982 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____24982
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
          ((let uu____25004 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____25004
            then
              let uu____25005 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____25005
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____25009 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____25009
             then
               let uu____25010 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____25010
             else ());
            (let f2 =
               let uu____25013 =
                 let uu____25014 = FStar_Syntax_Util.unmeta f1  in
                 uu____25014.FStar_Syntax_Syntax.n  in
               match uu____25013 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____25018 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___400_25019 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___400_25019.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___400_25019.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___400_25019.FStar_TypeChecker_Env.implicits)
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
            let uu____25073 =
              let uu____25074 =
                let uu____25075 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____25075;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____25074  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____25073
  
let with_guard_no_simp :
  'Auu____25090 .
    'Auu____25090 ->
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
            let uu____25113 =
              let uu____25114 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____25114;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____25113
  
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
          (let uu____25144 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____25144
           then
             let uu____25145 = FStar_Syntax_Print.term_to_string t1  in
             let uu____25146 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____25145
               uu____25146
           else ());
          (let uu____25148 =
             let uu____25153 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____25153
              in
           match uu____25148 with
           | (prob,wl) ->
               let g =
                 let uu____25161 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____25171  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____25161  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25205 = try_teq true env t1 t2  in
        match uu____25205 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25209 = FStar_TypeChecker_Env.get_range env  in
              let uu____25210 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25209 uu____25210);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25217 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25217
              then
                let uu____25218 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25219 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25220 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25218
                  uu____25219 uu____25220
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
          let uu____25242 = FStar_TypeChecker_Env.get_range env  in
          let uu____25243 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25242 uu____25243
  
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
        (let uu____25268 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25268
         then
           let uu____25269 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25270 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25269 uu____25270
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25273 =
           let uu____25280 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25280 "sub_comp"
            in
         match uu____25273 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25291 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25301  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25291)))
  
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
      fun uu____25346  ->
        match uu____25346 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25389 =
                 let uu____25394 =
                   let uu____25395 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25396 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25395 uu____25396
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25394)  in
               let uu____25397 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25389 uu____25397)
               in
            let equiv1 v1 v' =
              let uu____25409 =
                let uu____25414 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25415 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25414, uu____25415)  in
              match uu____25409 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25434 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25464 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25464 with
                      | FStar_Syntax_Syntax.U_unif uu____25471 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25500  ->
                                    match uu____25500 with
                                    | (u,v') ->
                                        let uu____25509 = equiv1 v1 v'  in
                                        if uu____25509
                                        then
                                          let uu____25512 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25512 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25528 -> []))
               in
            let uu____25533 =
              let wl =
                let uu___401_25537 = empty_worklist env  in
                {
                  attempting = (uu___401_25537.attempting);
                  wl_deferred = (uu___401_25537.wl_deferred);
                  ctr = (uu___401_25537.ctr);
                  defer_ok = false;
                  smt_ok = (uu___401_25537.smt_ok);
                  tcenv = (uu___401_25537.tcenv);
                  wl_implicits = (uu___401_25537.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25555  ->
                      match uu____25555 with
                      | (lb,v1) ->
                          let uu____25562 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25562 with
                           | USolved wl1 -> ()
                           | uu____25564 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25574 =
              match uu____25574 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25583) -> true
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
                      uu____25606,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25608,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25619) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25626,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25634 -> false)
               in
            let uu____25639 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25654  ->
                      match uu____25654 with
                      | (u,v1) ->
                          let uu____25661 = check_ineq (u, v1)  in
                          if uu____25661
                          then true
                          else
                            ((let uu____25664 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____25664
                              then
                                let uu____25665 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____25666 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____25665
                                  uu____25666
                              else ());
                             false)))
               in
            if uu____25639
            then ()
            else
              ((let uu____25670 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25670
                then
                  ((let uu____25672 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25672);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25682 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25682))
                else ());
               (let uu____25692 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25692))
  
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
        let fail1 uu____25759 =
          match uu____25759 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___402_25780 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___402_25780.attempting);
            wl_deferred = (uu___402_25780.wl_deferred);
            ctr = (uu___402_25780.ctr);
            defer_ok;
            smt_ok = (uu___402_25780.smt_ok);
            tcenv = (uu___402_25780.tcenv);
            wl_implicits = (uu___402_25780.wl_implicits)
          }  in
        (let uu____25782 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25782
         then
           let uu____25783 = FStar_Util.string_of_bool defer_ok  in
           let uu____25784 = wl_to_string wl  in
           let uu____25785 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____25783 uu____25784 uu____25785
         else ());
        (let g1 =
           let uu____25788 = solve_and_commit env wl fail1  in
           match uu____25788 with
           | FStar_Pervasives_Native.Some
               (uu____25795::uu____25796,uu____25797) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___403_25822 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___403_25822.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___403_25822.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____25823 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___404_25831 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___404_25831.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___404_25831.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___404_25831.FStar_TypeChecker_Env.implicits)
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
    let uu____25879 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25879 with
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
            let uu___405_25990 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___405_25990.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___405_25990.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___405_25990.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____25991 =
            let uu____25992 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____25992  in
          if uu____25991
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____26000 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____26001 =
                       let uu____26002 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____26002
                        in
                     FStar_Errors.diag uu____26000 uu____26001)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____26006 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____26007 =
                        let uu____26008 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____26008
                         in
                      FStar_Errors.diag uu____26006 uu____26007)
                   else ();
                   (let uu____26011 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____26011
                      "discharge_guard'" env vc1);
                   (let uu____26012 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____26012 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____26019 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26020 =
                                let uu____26021 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____26021
                                 in
                              FStar_Errors.diag uu____26019 uu____26020)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____26026 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26027 =
                                let uu____26028 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____26028
                                 in
                              FStar_Errors.diag uu____26026 uu____26027)
                           else ();
                           (let vcs =
                              let uu____26039 = FStar_Options.use_tactics ()
                                 in
                              if uu____26039
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____26059  ->
                                     (let uu____26061 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a236  -> ())
                                        uu____26061);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____26104  ->
                                              match uu____26104 with
                                              | (env1,goal,opts) ->
                                                  let uu____26120 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____26120, opts)))))
                              else
                                (let uu____26122 =
                                   let uu____26129 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____26129)  in
                                 [uu____26122])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____26162  ->
                                    match uu____26162 with
                                    | (env1,goal,opts) ->
                                        let uu____26172 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____26172 with
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
                                                (let uu____26180 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26181 =
                                                   let uu____26182 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____26183 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____26182 uu____26183
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26180 uu____26181)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____26186 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26187 =
                                                   let uu____26188 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____26188
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26186 uu____26187)
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
      let uu____26202 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26202 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26209 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26209
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26220 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26220 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____26237 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26237 with
      | FStar_Pervasives_Native.Some uu____26243 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26259 = try_teq false env t1 t2  in
        match uu____26259 with
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
            let uu____26289 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26289 with
            | FStar_Pervasives_Native.Some uu____26292 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26312 = acc  in
            match uu____26312 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26324 = hd1  in
                     (match uu____26324 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26329;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26337 = unresolved ctx_u  in
                             if uu____26337
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
                                       let uu___406_26353 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___406_26353.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           (uu___406_26353.FStar_TypeChecker_Env.imp_uvar);
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___406_26353.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___406_26353.FStar_TypeChecker_Env.imp_range);
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
                                    let uu___407_26361 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___407_26361.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___407_26361.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___407_26361.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___407_26361.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___407_26361.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___407_26361.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___407_26361.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___407_26361.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___407_26361.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___407_26361.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___407_26361.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___407_26361.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___407_26361.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___407_26361.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___407_26361.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___407_26361.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___407_26361.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___407_26361.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___407_26361.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___407_26361.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___407_26361.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___407_26361.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___407_26361.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___407_26361.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___407_26361.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___407_26361.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___407_26361.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___407_26361.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___407_26361.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___407_26361.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___407_26361.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___407_26361.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___407_26361.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___407_26361.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___407_26361.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___407_26361.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___407_26361.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___407_26361.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___407_26361.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___407_26361.FStar_TypeChecker_Env.dep_graph);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___407_26361.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___408_26364 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___408_26364.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___408_26364.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___408_26364.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___408_26364.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___408_26364.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___408_26364.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___408_26364.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___408_26364.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___408_26364.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___408_26364.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___408_26364.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___408_26364.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___408_26364.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___408_26364.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___408_26364.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___408_26364.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___408_26364.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___408_26364.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___408_26364.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___408_26364.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___408_26364.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___408_26364.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___408_26364.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___408_26364.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___408_26364.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___408_26364.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___408_26364.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___408_26364.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___408_26364.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___408_26364.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___408_26364.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___408_26364.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___408_26364.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___408_26364.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___408_26364.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___408_26364.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___408_26364.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___408_26364.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___408_26364.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___408_26364.FStar_TypeChecker_Env.dep_graph);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___408_26364.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26367 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26367
                                   then
                                     let uu____26368 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26369 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26370 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26371 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26368 uu____26369 uu____26370
                                       reason uu____26371
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___410_26375  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26382 =
                                             let uu____26391 =
                                               let uu____26398 =
                                                 let uu____26399 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26400 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26401 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26399 uu____26400
                                                   uu____26401
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26398, r)
                                                in
                                             [uu____26391]  in
                                           FStar_Errors.add_errors
                                             uu____26382);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___411_26415 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___411_26415.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___411_26415.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___411_26415.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26418 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26428  ->
                                               let uu____26429 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26430 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26431 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26429 uu____26430
                                                 reason uu____26431)) env2 g2
                                         true
                                        in
                                     match uu____26418 with
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
          let uu___412_26433 = g  in
          let uu____26434 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___412_26433.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___412_26433.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___412_26433.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26434
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
        let uu____26468 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26468 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26469 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a237  -> ()) uu____26469
      | imp::uu____26471 ->
          let uu____26474 =
            let uu____26479 =
              let uu____26480 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26481 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26480 uu____26481 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26479)
             in
          FStar_Errors.raise_error uu____26474
            imp.FStar_TypeChecker_Env.imp_range
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___413_26492 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___413_26492.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___413_26492.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___413_26492.FStar_TypeChecker_Env.implicits)
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
        (let uu____26527 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26527
         then
           let uu____26528 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26529 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26528
             uu____26529
         else ());
        (let uu____26531 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26531 with
         | (prob,x,wl) ->
             let g =
               let uu____26550 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26560  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26550  in
             ((let uu____26580 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26580
               then
                 let uu____26581 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26582 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26583 =
                   let uu____26584 = FStar_Util.must g  in
                   guard_to_string env uu____26584  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26581 uu____26582 uu____26583
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
        let uu____26618 = check_subtyping env t1 t2  in
        match uu____26618 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26637 =
              let uu____26638 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____26638 g  in
            FStar_Pervasives_Native.Some uu____26637
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26656 = check_subtyping env t1 t2  in
        match uu____26656 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26675 =
              let uu____26676 =
                let uu____26677 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26677]  in
              FStar_TypeChecker_Env.close_guard env uu____26676 g  in
            FStar_Pervasives_Native.Some uu____26675
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26712 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26712
         then
           let uu____26713 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26714 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26713
             uu____26714
         else ());
        (let uu____26716 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26716 with
         | (prob,x,wl) ->
             let g =
               let uu____26729 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____26739  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26729  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26760 =
                      let uu____26761 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26761]  in
                    FStar_TypeChecker_Env.close_guard env uu____26760 g1  in
                  discharge_guard_nosmt env g2))
  