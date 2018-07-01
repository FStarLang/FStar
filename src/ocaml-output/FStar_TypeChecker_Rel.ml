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
                    let uu___354_2507 = x  in
                    let uu____2508 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___354_2507.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___354_2507.FStar_Syntax_Syntax.index);
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
                      (fun uu___329_3965  ->
                         match uu___329_3965 with
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
                          (fun uu___330_4011  ->
                             match uu___330_4011 with
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
                               (fun uu___331_4077  ->
                                  match uu___331_4077 with
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
             (let uu___355_4832 = wl1  in
              {
                attempting = (uu___355_4832.attempting);
                wl_deferred = (uu___355_4832.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___355_4832.defer_ok);
                smt_ok = (uu___355_4832.smt_ok);
                tcenv = (uu___355_4832.tcenv);
                wl_implicits = (uu___355_4832.wl_implicits)
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
        (let uu___356_4863 = wl  in
         {
           attempting = (uu___356_4863.attempting);
           wl_deferred = (uu___356_4863.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___356_4863.defer_ok);
           smt_ok = (uu___356_4863.smt_ok);
           tcenv = (uu___356_4863.tcenv);
           wl_implicits = (uu___356_4863.wl_implicits)
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
              (fun uu___332_5350  ->
                 match uu___332_5350 with
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
  
let string_of_option :
  'Auu____6276 .
    ('Auu____6276 -> Prims.string) ->
      'Auu____6276 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___333_6291  ->
      match uu___333_6291 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6297 = f x  in Prims.strcat "Some " uu____6297
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___334_6302  ->
    match uu___334_6302 with
    | MisMatch (d1,d2) ->
        let uu____6313 =
          let uu____6314 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6315 =
            let uu____6316 =
              let uu____6317 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6317 ")"  in
            Prims.strcat ") (" uu____6316  in
          Prims.strcat uu____6314 uu____6315  in
        Prims.strcat "MisMatch (" uu____6313
    | HeadMatch u ->
        let uu____6319 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6319
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___335_6324  ->
    match uu___335_6324 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6339 -> HeadMatch false
  
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
          let uu____6353 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6353 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6364 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6387 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6396 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6422 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6422
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6423 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6424 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6425 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6438 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6451 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6475) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6481,uu____6482) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6524) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6549;
             FStar_Syntax_Syntax.index = uu____6550;
             FStar_Syntax_Syntax.sort = t2;_},uu____6552)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6559 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6560 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6561 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6576 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6583 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6603 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6603
  
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
            let uu____6630 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6630
            then FullMatch
            else
              (let uu____6632 =
                 let uu____6641 =
                   let uu____6644 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6644  in
                 let uu____6645 =
                   let uu____6648 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6648  in
                 (uu____6641, uu____6645)  in
               MisMatch uu____6632)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6654),FStar_Syntax_Syntax.Tm_uinst (g,uu____6656)) ->
            let uu____6665 = head_matches env f g  in
            FStar_All.pipe_right uu____6665 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6668 = FStar_Const.eq_const c d  in
            if uu____6668
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6675),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6677)) ->
            let uu____6710 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6710
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6717),FStar_Syntax_Syntax.Tm_refine (y,uu____6719)) ->
            let uu____6728 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6728 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6730),uu____6731) ->
            let uu____6736 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6736 head_match
        | (uu____6737,FStar_Syntax_Syntax.Tm_refine (x,uu____6739)) ->
            let uu____6744 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6744 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6745,FStar_Syntax_Syntax.Tm_type
           uu____6746) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6747,FStar_Syntax_Syntax.Tm_arrow uu____6748) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6778),FStar_Syntax_Syntax.Tm_app (head',uu____6780))
            ->
            let uu____6829 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6829 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6831),uu____6832) ->
            let uu____6857 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6857 head_match
        | (uu____6858,FStar_Syntax_Syntax.Tm_app (head1,uu____6860)) ->
            let uu____6885 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6885 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6886,FStar_Syntax_Syntax.Tm_let
           uu____6887) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6912,FStar_Syntax_Syntax.Tm_match uu____6913) ->
            HeadMatch true
        | uu____6958 ->
            let uu____6963 =
              let uu____6972 = delta_depth_of_term env t11  in
              let uu____6975 = delta_depth_of_term env t21  in
              (uu____6972, uu____6975)  in
            MisMatch uu____6963
  
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
          (let uu____7035 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7035
           then
             let uu____7036 = FStar_Syntax_Print.term_to_string t  in
             let uu____7037 = FStar_Syntax_Print.term_to_string head1  in
             FStar_Util.print2 "Head of %s is %s\n" uu____7036 uu____7037
           else ());
          (let uu____7039 =
             let uu____7040 = FStar_Syntax_Util.un_uinst head1  in
             uu____7040.FStar_Syntax_Syntax.n  in
           match uu____7039 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____7046 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant;
                   FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____7046 with
                | FStar_Pervasives_Native.None  ->
                    ((let uu____7060 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7060
                      then
                        let uu____7061 =
                          FStar_Syntax_Print.term_to_string head1  in
                        FStar_Util.print1 "No definition found for %s\n"
                          uu____7061
                      else ());
                     FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.Some uu____7063 ->
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
                    ((let uu____7074 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7074
                      then
                        let uu____7075 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____7076 = FStar_Syntax_Print.term_to_string t'
                           in
                        FStar_Util.print2 "Inlined %s to %s\n" uu____7075
                          uu____7076
                      else ());
                     FStar_Pervasives_Native.Some t'))
           | uu____7078 -> FStar_Pervasives_Native.None)
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
          (let uu____7216 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7216
           then
             let uu____7217 = FStar_Syntax_Print.term_to_string t11  in
             let uu____7218 = FStar_Syntax_Print.term_to_string t21  in
             let uu____7219 = string_of_match_result r  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7217
               uu____7218 uu____7219
           else ());
          (let reduce_one_and_try_again d1 d2 =
             let d1_greater_than_d2 =
               FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
             let uu____7243 =
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
             match uu____7243 with
             | (t12,t22) ->
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           let reduce_both_and_try_again d r1 =
             let uu____7288 = FStar_TypeChecker_Common.decr_delta_depth d  in
             match uu____7288 with
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
                uu____7320),uu____7321)
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7339 =
                    let uu____7348 = maybe_inline t11  in
                    let uu____7351 = maybe_inline t21  in
                    (uu____7348, uu____7351)  in
                  match uu____7339 with
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
               (uu____7388,FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level uu____7389))
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7407 =
                    let uu____7416 = maybe_inline t11  in
                    let uu____7419 = maybe_inline t21  in
                    (uu____7416, uu____7419)  in
                  match uu____7407 with
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
           | MisMatch uu____7468 -> fail1 n_delta r t11 t21
           | uu____7477 -> success n_delta r t11 t21)
           in
        let r = aux true (Prims.parse_int "0") t1 t2  in
        (let uu____7490 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelDelta")
            in
         if uu____7490
         then
           let uu____7491 = FStar_Syntax_Print.term_to_string t1  in
           let uu____7492 = FStar_Syntax_Print.term_to_string t2  in
           let uu____7493 =
             string_of_match_result (FStar_Pervasives_Native.fst r)  in
           let uu____7500 =
             if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
             then "None"
             else
               (let uu____7512 =
                  FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____7512
                  (fun uu____7546  ->
                     match uu____7546 with
                     | (t11,t21) ->
                         let uu____7553 =
                           FStar_Syntax_Print.term_to_string t11  in
                         let uu____7554 =
                           let uu____7555 =
                             FStar_Syntax_Print.term_to_string t21  in
                           Prims.strcat "; " uu____7555  in
                         Prims.strcat uu____7553 uu____7554))
              in
           FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
             uu____7491 uu____7492 uu____7493 uu____7500
         else ());
        r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7567 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7567 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___336_7580  ->
    match uu___336_7580 with
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
      let uu___357_7617 = p  in
      let uu____7620 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7621 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___357_7617.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7620;
        FStar_TypeChecker_Common.relation =
          (uu___357_7617.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7621;
        FStar_TypeChecker_Common.element =
          (uu___357_7617.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___357_7617.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___357_7617.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___357_7617.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___357_7617.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___357_7617.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7635 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7635
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7640 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7662 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7662 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7670 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7670 with
           | (lh,lhs_args) ->
               let uu____7717 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7717 with
                | (rh,rhs_args) ->
                    let uu____7764 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7777,FStar_Syntax_Syntax.Tm_uvar uu____7778)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7867 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7894,uu____7895)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7910,FStar_Syntax_Syntax.Tm_uvar uu____7911)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7926,FStar_Syntax_Syntax.Tm_arrow uu____7927)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_7957 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_7957.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_7957.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_7957.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_7957.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_7957.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_7957.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_7957.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_7957.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_7957.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7960,FStar_Syntax_Syntax.Tm_type uu____7961)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_7977 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_7977.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_7977.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_7977.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_7977.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_7977.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_7977.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_7977.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_7977.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_7977.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7980,FStar_Syntax_Syntax.Tm_uvar uu____7981)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___358_7997 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___358_7997.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___358_7997.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___358_7997.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___358_7997.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___358_7997.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___358_7997.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___358_7997.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___358_7997.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___358_7997.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8000,FStar_Syntax_Syntax.Tm_uvar uu____8001)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8016,uu____8017)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8032,FStar_Syntax_Syntax.Tm_uvar uu____8033)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8048,uu____8049) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7764 with
                     | (rank,tp1) ->
                         let uu____8062 =
                           FStar_All.pipe_right
                             (let uu___359_8066 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___359_8066.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___359_8066.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___359_8066.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___359_8066.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___359_8066.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___359_8066.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___359_8066.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___359_8066.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___359_8066.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____8062))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8072 =
            FStar_All.pipe_right
              (let uu___360_8076 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___360_8076.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___360_8076.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___360_8076.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___360_8076.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___360_8076.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___360_8076.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___360_8076.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___360_8076.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___360_8076.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8072)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8137 probs =
      match uu____8137 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8218 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8239 = rank wl.tcenv hd1  in
               (match uu____8239 with
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
                      (let uu____8298 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8302 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8302)
                          in
                       if uu____8298
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
          let uu____8370 = FStar_Syntax_Util.head_and_args t  in
          match uu____8370 with
          | (hd1,uu____8388) ->
              let uu____8413 =
                let uu____8414 = FStar_Syntax_Subst.compress hd1  in
                uu____8414.FStar_Syntax_Syntax.n  in
              (match uu____8413 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8418) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8452  ->
                           match uu____8452 with
                           | (y,uu____8460) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8482  ->
                                       match uu____8482 with
                                       | (x,uu____8490) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8495 -> false)
           in
        let uu____8496 = rank tcenv p  in
        match uu____8496 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8503 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8530 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8544 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8558 -> false
  
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
                        let uu____8610 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8610 with
                        | (k,uu____8616) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8626 -> false)))
            | uu____8627 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8679 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8685 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8685 = (Prims.parse_int "0")))
                           in
                        if uu____8679 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8701 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8707 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8707 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8701)
               in
            let uu____8708 = filter1 u12  in
            let uu____8711 = filter1 u22  in (uu____8708, uu____8711)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8740 = filter_out_common_univs us1 us2  in
                (match uu____8740 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8799 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8799 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8802 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8812 =
                          let uu____8813 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8814 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8813
                            uu____8814
                           in
                        UFailed uu____8812))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8838 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8838 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8864 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8864 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8867 ->
                let uu____8872 =
                  let uu____8873 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8874 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8873
                    uu____8874 msg
                   in
                UFailed uu____8872
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8875,uu____8876) ->
              let uu____8877 =
                let uu____8878 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8879 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8878 uu____8879
                 in
              failwith uu____8877
          | (FStar_Syntax_Syntax.U_unknown ,uu____8880) ->
              let uu____8881 =
                let uu____8882 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8883 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8882 uu____8883
                 in
              failwith uu____8881
          | (uu____8884,FStar_Syntax_Syntax.U_bvar uu____8885) ->
              let uu____8886 =
                let uu____8887 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8888 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8887 uu____8888
                 in
              failwith uu____8886
          | (uu____8889,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8890 =
                let uu____8891 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8892 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8891 uu____8892
                 in
              failwith uu____8890
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8916 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8916
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8930 = occurs_univ v1 u3  in
              if uu____8930
              then
                let uu____8931 =
                  let uu____8932 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8933 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8932 uu____8933
                   in
                try_umax_components u11 u21 uu____8931
              else
                (let uu____8935 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8935)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8947 = occurs_univ v1 u3  in
              if uu____8947
              then
                let uu____8948 =
                  let uu____8949 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8950 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8949 uu____8950
                   in
                try_umax_components u11 u21 uu____8948
              else
                (let uu____8952 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8952)
          | (FStar_Syntax_Syntax.U_max uu____8953,uu____8954) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8960 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8960
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8962,FStar_Syntax_Syntax.U_max uu____8963) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8969 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8969
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8971,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8972,FStar_Syntax_Syntax.U_name
             uu____8973) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8974) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8975) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8976,FStar_Syntax_Syntax.U_succ
             uu____8977) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8978,FStar_Syntax_Syntax.U_zero
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
      let uu____9078 = bc1  in
      match uu____9078 with
      | (bs1,mk_cod1) ->
          let uu____9122 = bc2  in
          (match uu____9122 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9233 = aux xs ys  in
                     (match uu____9233 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9316 =
                       let uu____9323 = mk_cod1 xs  in ([], uu____9323)  in
                     let uu____9326 =
                       let uu____9333 = mk_cod2 ys  in ([], uu____9333)  in
                     (uu____9316, uu____9326)
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
                  let uu____9401 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9401 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9404 =
                    let uu____9405 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9405 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9404
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9410 = has_type_guard t1 t2  in (uu____9410, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9411 = has_type_guard t2 t1  in (uu____9411, wl)
  
let is_flex_pat :
  'Auu____9420 'Auu____9421 'Auu____9422 .
    ('Auu____9420,'Auu____9421,'Auu____9422 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___337_9435  ->
    match uu___337_9435 with
    | (uu____9444,uu____9445,[]) -> true
    | uu____9448 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9479 = f  in
      match uu____9479 with
      | (uu____9486,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9487;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9488;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9491;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9492;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9493;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9553  ->
                 match uu____9553 with
                 | (y,uu____9561) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9715 =
                  let uu____9730 =
                    let uu____9733 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9733  in
                  ((FStar_List.rev pat_binders), uu____9730)  in
                FStar_Pervasives_Native.Some uu____9715
            | (uu____9766,[]) ->
                let uu____9797 =
                  let uu____9812 =
                    let uu____9815 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9815  in
                  ((FStar_List.rev pat_binders), uu____9812)  in
                FStar_Pervasives_Native.Some uu____9797
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9906 =
                  let uu____9907 = FStar_Syntax_Subst.compress a  in
                  uu____9907.FStar_Syntax_Syntax.n  in
                (match uu____9906 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9927 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9927
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___361_9954 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___361_9954.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___361_9954.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9958 =
                            let uu____9959 =
                              let uu____9966 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9966)  in
                            FStar_Syntax_Syntax.NT uu____9959  in
                          [uu____9958]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___362_9982 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___362_9982.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___362_9982.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9983 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____10023 =
                  let uu____10038 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10038  in
                (match uu____10023 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10113 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10146 ->
               let uu____10147 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10147 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10431 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10431
       then
         let uu____10432 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10432
       else ());
      (let uu____10434 = next_prob probs  in
       match uu____10434 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___363_10461 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___363_10461.wl_deferred);
               ctr = (uu___363_10461.ctr);
               defer_ok = (uu___363_10461.defer_ok);
               smt_ok = (uu___363_10461.smt_ok);
               tcenv = (uu___363_10461.tcenv);
               wl_implicits = (uu___363_10461.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10469 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10469
                 then
                   let uu____10470 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10470
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
                           (let uu___364_10475 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___364_10475.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___364_10475.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___364_10475.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___364_10475.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___364_10475.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___364_10475.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___364_10475.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___364_10475.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___364_10475.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10497 ->
                let uu____10506 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10565  ->
                          match uu____10565 with
                          | (c,uu____10573,uu____10574) -> c < probs.ctr))
                   in
                (match uu____10506 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10615 =
                            let uu____10620 =
                              FStar_List.map
                                (fun uu____10635  ->
                                   match uu____10635 with
                                   | (uu____10646,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10620, (probs.wl_implicits))  in
                          Success uu____10615
                      | uu____10649 ->
                          let uu____10658 =
                            let uu___365_10659 = probs  in
                            let uu____10660 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10679  ->
                                      match uu____10679 with
                                      | (uu____10686,uu____10687,y) -> y))
                               in
                            {
                              attempting = uu____10660;
                              wl_deferred = rest;
                              ctr = (uu___365_10659.ctr);
                              defer_ok = (uu___365_10659.defer_ok);
                              smt_ok = (uu___365_10659.smt_ok);
                              tcenv = (uu___365_10659.tcenv);
                              wl_implicits = (uu___365_10659.wl_implicits)
                            }  in
                          solve env uu____10658))))

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
            let uu____10694 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10694 with
            | USolved wl1 ->
                let uu____10696 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10696
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
                  let uu____10748 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10748 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10751 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10763;
                  FStar_Syntax_Syntax.vars = uu____10764;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10767;
                  FStar_Syntax_Syntax.vars = uu____10768;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10780,uu____10781) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10788,FStar_Syntax_Syntax.Tm_uinst uu____10789) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10796 -> USolved wl

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
            ((let uu____10806 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10806
              then
                let uu____10807 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10807 msg
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
               let uu____10893 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10893 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10946 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10946
                then
                  let uu____10947 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10948 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10947 uu____10948
                else ());
               (let uu____10950 = head_matches_delta env1 t1 t2  in
                match uu____10950 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10995 = eq_prob t1 t2 wl2  in
                         (match uu____10995 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11016 ->
                         let uu____11025 = eq_prob t1 t2 wl2  in
                         (match uu____11025 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11074 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11089 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11090 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11089, uu____11090)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11095 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11096 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11095, uu____11096)
                            in
                         (match uu____11074 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11127 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11127 with
                                | (t1_hd,t1_args) ->
                                    let uu____11172 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11172 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11236 =
                                              let uu____11243 =
                                                let uu____11254 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11254 :: t1_args  in
                                              let uu____11271 =
                                                let uu____11280 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11280 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11329  ->
                                                   fun uu____11330  ->
                                                     fun uu____11331  ->
                                                       match (uu____11329,
                                                               uu____11330,
                                                               uu____11331)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11381),
                                                          (a2,uu____11383))
                                                           ->
                                                           let uu____11420 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11420
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11243
                                                uu____11271
                                               in
                                            match uu____11236 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___366_11446 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___366_11446.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___366_11446.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11454 =
                                                  solve env1 wl'  in
                                                (match uu____11454 with
                                                 | Success (uu____11457,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___367_11461
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___367_11461.attempting);
                                                            wl_deferred =
                                                              (uu___367_11461.wl_deferred);
                                                            ctr =
                                                              (uu___367_11461.ctr);
                                                            defer_ok =
                                                              (uu___367_11461.defer_ok);
                                                            smt_ok =
                                                              (uu___367_11461.smt_ok);
                                                            tcenv =
                                                              (uu___367_11461.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11462 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11494 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11494 with
                                | (t1_base,p1_opt) ->
                                    let uu____11541 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11541 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11651 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11651
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
                                               let uu____11699 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11699
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
                                               let uu____11729 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11729
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
                                               let uu____11759 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11759
                                           | uu____11762 -> t_base  in
                                         let uu____11779 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11779 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11793 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11793, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11800 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11800 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11847 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11847 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11894 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11894
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
                              let uu____11918 = combine t11 t21 wl2  in
                              (match uu____11918 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11951 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11951
                                     then
                                       let uu____11952 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11952
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11991 ts1 =
               match uu____11991 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12054 = pairwise out t wl2  in
                        (match uu____12054 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12090 =
               let uu____12101 = FStar_List.hd ts  in (uu____12101, [], wl1)
                in
             let uu____12110 = FStar_List.tl ts  in
             aux uu____12090 uu____12110  in
           let uu____12117 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12117 with
           | (this_flex,this_rigid) ->
               let uu____12141 =
                 let uu____12142 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12142.FStar_Syntax_Syntax.n  in
               (match uu____12141 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12167 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12167
                    then
                      let uu____12168 = destruct_flex_t this_flex wl  in
                      (match uu____12168 with
                       | (flex,wl1) ->
                           let uu____12175 = quasi_pattern env flex  in
                           (match uu____12175 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12193 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12193
                                  then
                                    let uu____12194 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12194
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12197 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___368_12200 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___368_12200.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___368_12200.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___368_12200.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___368_12200.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___368_12200.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___368_12200.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___368_12200.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___368_12200.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___368_12200.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12197)
                | uu____12201 ->
                    ((let uu____12203 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12203
                      then
                        let uu____12204 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12204
                      else ());
                     (let uu____12206 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12206 with
                      | (u,_args) ->
                          let uu____12249 =
                            let uu____12250 = FStar_Syntax_Subst.compress u
                               in
                            uu____12250.FStar_Syntax_Syntax.n  in
                          (match uu____12249 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12277 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12277 with
                                 | (u',uu____12295) ->
                                     let uu____12320 =
                                       let uu____12321 = whnf env u'  in
                                       uu____12321.FStar_Syntax_Syntax.n  in
                                     (match uu____12320 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12342 -> false)
                                  in
                               let uu____12343 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___338_12366  ->
                                         match uu___338_12366 with
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
                                              | uu____12375 -> false)
                                         | uu____12378 -> false))
                                  in
                               (match uu____12343 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12392 = whnf env this_rigid
                                         in
                                      let uu____12393 =
                                        FStar_List.collect
                                          (fun uu___339_12399  ->
                                             match uu___339_12399 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12405 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12405]
                                             | uu____12407 -> [])
                                          bounds_probs
                                         in
                                      uu____12392 :: uu____12393  in
                                    let uu____12408 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12408 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12439 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12454 =
                                               let uu____12455 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12455.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12454 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12467 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12467)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12476 -> bound  in
                                           let uu____12477 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12477)  in
                                         (match uu____12439 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12506 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12506
                                                then
                                                  let wl'1 =
                                                    let uu___369_12508 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___369_12508.wl_deferred);
                                                      ctr =
                                                        (uu___369_12508.ctr);
                                                      defer_ok =
                                                        (uu___369_12508.defer_ok);
                                                      smt_ok =
                                                        (uu___369_12508.smt_ok);
                                                      tcenv =
                                                        (uu___369_12508.tcenv);
                                                      wl_implicits =
                                                        (uu___369_12508.wl_implicits)
                                                    }  in
                                                  let uu____12509 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12509
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12512 =
                                                  solve_t env eq_prob
                                                    (let uu___370_12514 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___370_12514.wl_deferred);
                                                       ctr =
                                                         (uu___370_12514.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___370_12514.smt_ok);
                                                       tcenv =
                                                         (uu___370_12514.tcenv);
                                                       wl_implicits =
                                                         (uu___370_12514.wl_implicits)
                                                     })
                                                   in
                                                match uu____12512 with
                                                | Success uu____12515 ->
                                                    let wl2 =
                                                      let uu___371_12521 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___371_12521.wl_deferred);
                                                        ctr =
                                                          (uu___371_12521.ctr);
                                                        defer_ok =
                                                          (uu___371_12521.defer_ok);
                                                        smt_ok =
                                                          (uu___371_12521.smt_ok);
                                                        tcenv =
                                                          (uu___371_12521.tcenv);
                                                        wl_implicits =
                                                          (uu___371_12521.wl_implicits)
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
                                                    let uu____12536 =
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
                                                    ((let uu____12547 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12547
                                                      then
                                                        let uu____12548 =
                                                          let uu____12549 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12549
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12548
                                                      else ());
                                                     (let uu____12555 =
                                                        let uu____12570 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12570)
                                                         in
                                                      match uu____12555 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12592))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12618 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12618
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
                                                                  let uu____12635
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12635))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12660 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12660
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
                                                                    let uu____12678
                                                                    =
                                                                    let uu____12683
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12683
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12678
                                                                    [] wl2
                                                                     in
                                                                  let uu____12688
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12688))))
                                                      | uu____12689 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12704 when flip ->
                               let uu____12705 =
                                 let uu____12706 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12707 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12706 uu____12707
                                  in
                               failwith uu____12705
                           | uu____12708 ->
                               let uu____12709 =
                                 let uu____12710 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12711 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12710 uu____12711
                                  in
                               failwith uu____12709)))))

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
                      (fun uu____12745  ->
                         match uu____12745 with
                         | (x,i) ->
                             let uu____12764 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12764, i)) bs_lhs
                     in
                  let uu____12767 = lhs  in
                  match uu____12767 with
                  | (uu____12768,u_lhs,uu____12770) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12867 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12877 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12877, univ)
                             in
                          match uu____12867 with
                          | (k,univ) ->
                              let uu____12884 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12884 with
                               | (uu____12901,u,wl3) ->
                                   let uu____12904 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12904, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12930 =
                              let uu____12943 =
                                let uu____12954 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12954 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____13005  ->
                                   fun uu____13006  ->
                                     match (uu____13005, uu____13006) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13107 =
                                           let uu____13114 =
                                             let uu____13117 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13117
                                              in
                                           copy_uvar u_lhs [] uu____13114 wl2
                                            in
                                         (match uu____13107 with
                                          | (uu____13146,t_a,wl3) ->
                                              let uu____13149 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13149 with
                                               | (uu____13168,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12943
                                ([], wl1)
                               in
                            (match uu____12930 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___372_13224 = ct  in
                                   let uu____13225 =
                                     let uu____13228 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13228
                                      in
                                   let uu____13243 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___372_13224.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___372_13224.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13225;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13243;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___372_13224.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___373_13261 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___373_13261.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___373_13261.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13264 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13264 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13326 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13326 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13337 =
                                          let uu____13342 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13342)  in
                                        TERM uu____13337  in
                                      let uu____13343 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13343 with
                                       | (sub_prob,wl3) ->
                                           let uu____13356 =
                                             let uu____13357 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13357
                                              in
                                           solve env uu____13356))
                             | (x,imp)::formals2 ->
                                 let uu____13379 =
                                   let uu____13386 =
                                     let uu____13389 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13389
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13386 wl1
                                    in
                                 (match uu____13379 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13410 =
                                          let uu____13413 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13413
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13410 u_x
                                         in
                                      let uu____13414 =
                                        let uu____13417 =
                                          let uu____13420 =
                                            let uu____13421 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13421, imp)  in
                                          [uu____13420]  in
                                        FStar_List.append bs_terms
                                          uu____13417
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13414 formals2 wl2)
                              in
                           let uu____13448 = occurs_check u_lhs arrow1  in
                           (match uu____13448 with
                            | (uu____13459,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13470 =
                                    let uu____13471 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13471
                                     in
                                  giveup_or_defer env orig wl uu____13470
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
              (let uu____13500 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13500
               then
                 let uu____13501 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13502 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13501 (rel_to_string (p_rel orig)) uu____13502
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13623 = rhs wl1 scope env1 subst1  in
                     (match uu____13623 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13643 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13643
                            then
                              let uu____13644 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13644
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____13717 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____13717 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___374_13719 = hd1  in
                       let uu____13720 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___374_13719.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___374_13719.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13720
                       }  in
                     let hd21 =
                       let uu___375_13724 = hd2  in
                       let uu____13725 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___375_13724.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___375_13724.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13725
                       }  in
                     let uu____13728 =
                       let uu____13733 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13733
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13728 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13752 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13752
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13756 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13756 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13819 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13819
                                  in
                               ((let uu____13837 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13837
                                 then
                                   let uu____13838 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13839 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13838
                                     uu____13839
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13866 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13899 = aux wl [] env [] bs1 bs2  in
               match uu____13899 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13948 = attempt sub_probs wl2  in
                   solve env uu____13948)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13953 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13953 wl)

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
              let uu____13967 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13967 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____14001 = lhs1  in
              match uu____14001 with
              | (uu____14004,ctx_u,uu____14006) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____14014 ->
                        let uu____14015 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____14015 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____14062 = quasi_pattern env1 lhs1  in
              match uu____14062 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____14092) ->
                  let uu____14097 = lhs1  in
                  (match uu____14097 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____14111 = occurs_check ctx_u rhs1  in
                       (match uu____14111 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14153 =
                                let uu____14160 =
                                  let uu____14161 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14161
                                   in
                                FStar_Util.Inl uu____14160  in
                              (uu____14153, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14183 =
                                 let uu____14184 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14184  in
                               if uu____14183
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14204 =
                                    let uu____14211 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14211  in
                                  let uu____14216 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14204, uu____14216)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14284  ->
                     match uu____14284 with
                     | (x,i) ->
                         let uu____14303 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14303, i)) bs_lhs
                 in
              let uu____14306 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14306 with
              | (rhs_hd,args) ->
                  let uu____14349 = FStar_Util.prefix args  in
                  (match uu____14349 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14421 = lhs1  in
                       (match uu____14421 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14425 =
                              let uu____14436 =
                                let uu____14443 =
                                  let uu____14446 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14446
                                   in
                                copy_uvar u_lhs [] uu____14443 wl1  in
                              match uu____14436 with
                              | (uu____14473,t_last_arg,wl2) ->
                                  let uu____14476 =
                                    let uu____14483 =
                                      let uu____14484 =
                                        let uu____14493 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14493]  in
                                      FStar_List.append bs_lhs uu____14484
                                       in
                                    copy_uvar u_lhs uu____14483 t_res_lhs wl2
                                     in
                                  (match uu____14476 with
                                   | (uu____14528,lhs',wl3) ->
                                       let uu____14531 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14531 with
                                        | (uu____14548,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14425 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14569 =
                                     let uu____14570 =
                                       let uu____14575 =
                                         let uu____14576 =
                                           let uu____14579 =
                                             let uu____14584 =
                                               let uu____14585 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14585]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14584
                                              in
                                           uu____14579
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14576
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14575)  in
                                     TERM uu____14570  in
                                   [uu____14569]  in
                                 let uu____14612 =
                                   let uu____14619 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14619 with
                                   | (p1,wl3) ->
                                       let uu____14638 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14638 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14612 with
                                  | (sub_probs,wl3) ->
                                      let uu____14669 =
                                        let uu____14670 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14670  in
                                      solve env1 uu____14669))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14703 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14703 with
                | (uu____14720,args) ->
                    (match args with | [] -> false | uu____14754 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14771 =
                  let uu____14772 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14772.FStar_Syntax_Syntax.n  in
                match uu____14771 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14775 -> true
                | uu____14790 -> false  in
              let uu____14791 = quasi_pattern env1 lhs1  in
              match uu____14791 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14802 =
                    let uu____14803 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14803
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14802
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14810 = is_app rhs1  in
                  if uu____14810
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14812 = is_arrow rhs1  in
                     if uu____14812
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14814 =
                          let uu____14815 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14815
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14814))
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
                let uu____14818 = lhs  in
                (match uu____14818 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14822 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14822 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14839 =
                              let uu____14842 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14842
                               in
                            FStar_All.pipe_right uu____14839
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14859 = occurs_check ctx_uv rhs1  in
                          (match uu____14859 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14881 =
                                   let uu____14882 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14882
                                    in
                                 giveup_or_defer env orig wl uu____14881
                               else
                                 (let uu____14884 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14884
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14889 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14889
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14891 =
                                         let uu____14892 =
                                           names_to_string1 fvs2  in
                                         let uu____14893 =
                                           names_to_string1 fvs1  in
                                         let uu____14894 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14892 uu____14893
                                           uu____14894
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14891)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14902 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14906 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14906 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14929 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14929
                             | (FStar_Util.Inl msg,uu____14931) ->
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
                  (let uu____14964 =
                     let uu____14981 = quasi_pattern env lhs  in
                     let uu____14988 = quasi_pattern env rhs  in
                     (uu____14981, uu____14988)  in
                   match uu____14964 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____15031 = lhs  in
                       (match uu____15031 with
                        | ({ FStar_Syntax_Syntax.n = uu____15032;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____15034;_},u_lhs,uu____15036)
                            ->
                            let uu____15039 = rhs  in
                            (match uu____15039 with
                             | (uu____15040,u_rhs,uu____15042) ->
                                 let uu____15043 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____15043
                                 then
                                   let uu____15048 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____15048
                                 else
                                   (let uu____15050 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____15050 with
                                    | (sub_prob,wl1) ->
                                        let uu____15063 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____15063 with
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
                                             let uu____15095 =
                                               let uu____15102 =
                                                 let uu____15105 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____15105
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
                                                 uu____15102
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____15095 with
                                              | (uu____15108,w,wl2) ->
                                                  let w_app =
                                                    let uu____15114 =
                                                      let uu____15119 =
                                                        FStar_List.map
                                                          (fun uu____15130 
                                                             ->
                                                             match uu____15130
                                                             with
                                                             | (z,uu____15138)
                                                                 ->
                                                                 let uu____15143
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____15143)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____15119
                                                       in
                                                    uu____15114
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____15147 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____15147
                                                    then
                                                      let uu____15148 =
                                                        let uu____15151 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____15152 =
                                                          let uu____15155 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____15156 =
                                                            let uu____15159 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____15160 =
                                                              let uu____15163
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____15170
                                                                =
                                                                let uu____15173
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____15180
                                                                  =
                                                                  let uu____15183
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____15183]
                                                                   in
                                                                uu____15173
                                                                  ::
                                                                  uu____15180
                                                                 in
                                                              uu____15163 ::
                                                                uu____15170
                                                               in
                                                            uu____15159 ::
                                                              uu____15160
                                                             in
                                                          uu____15155 ::
                                                            uu____15156
                                                           in
                                                        uu____15151 ::
                                                          uu____15152
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____15148
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____15189 =
                                                          let uu____15194 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____15194)
                                                           in
                                                        TERM uu____15189  in
                                                      let uu____15195 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____15195
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____15200 =
                                                             let uu____15205
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
                                                               uu____15205)
                                                              in
                                                           TERM uu____15200
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____15206 =
                                                      let uu____15207 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____15207
                                                       in
                                                    solve env uu____15206)))))))
                   | uu____15208 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____15272 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15272
            then
              let uu____15273 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15274 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15275 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15276 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15273 uu____15274 uu____15275 uu____15276
            else ());
           (let uu____15279 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15279 with
            | (head1,args1) ->
                let uu____15322 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15322 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15386 =
                         let uu____15387 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15388 = args_to_string args1  in
                         let uu____15391 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15392 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15387 uu____15388 uu____15391 uu____15392
                          in
                       giveup env1 uu____15386 orig
                     else
                       (let uu____15396 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15402 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15402 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15396
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___376_15404 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___376_15404.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___376_15404.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___376_15404.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___376_15404.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___376_15404.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___376_15404.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___376_15404.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___376_15404.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____15406 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____15406 with
                              | USolved wl2 ->
                                  let uu____15408 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____15408
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____15412 = base_and_refinement env1 t1  in
                           match uu____15412 with
                           | (base1,refinement1) ->
                               let uu____15437 = base_and_refinement env1 t2
                                  in
                               (match uu____15437 with
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
                                           let uu____15557 =
                                             FStar_List.fold_right
                                               (fun uu____15597  ->
                                                  fun uu____15598  ->
                                                    match (uu____15597,
                                                            uu____15598)
                                                    with
                                                    | (((a1,uu____15650),
                                                        (a2,uu____15652)),
                                                       (probs,wl2)) ->
                                                        let uu____15701 =
                                                          let uu____15708 =
                                                            p_scope orig  in
                                                          mk_problem wl2
                                                            uu____15708 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15701
                                                         with
                                                         | (prob',wl3) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl3)))
                                               argp ([], wl1)
                                              in
                                           (match uu____15557 with
                                            | (subprobs,wl2) ->
                                                ((let uu____15740 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____15740
                                                  then
                                                    let uu____15741 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____15741
                                                  else ());
                                                 (let formula =
                                                    let uu____15746 =
                                                      FStar_List.map
                                                        (fun p  -> p_guard p)
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____15746
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  let uu____15754 =
                                                    attempt subprobs wl3  in
                                                  solve env1 uu____15754)))
                                         else
                                           (let uu____15756 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____15756 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let uu____15760 =
                                                  FStar_List.fold_right2
                                                    (fun uu____15797  ->
                                                       fun uu____15798  ->
                                                         fun uu____15799  ->
                                                           match (uu____15797,
                                                                   uu____15798,
                                                                   uu____15799)
                                                           with
                                                           | ((a,uu____15843),
                                                              (a',uu____15845),
                                                              (subprobs,wl3))
                                                               ->
                                                               let uu____15878
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 []
                                                                   orig a
                                                                   FStar_TypeChecker_Common.EQ
                                                                   a'
                                                                   FStar_Pervasives_Native.None
                                                                   "index"
                                                                  in
                                                               (match uu____15878
                                                                with
                                                                | (p,wl4) ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                    args1 args2 ([], wl2)
                                                   in
                                                (match uu____15760 with
                                                 | (subprobs,wl3) ->
                                                     ((let uu____15908 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           (FStar_Options.Other
                                                              "Rel")
                                                          in
                                                       if uu____15908
                                                       then
                                                         let uu____15909 =
                                                           FStar_Syntax_Print.list_to_string
                                                             (prob_to_string
                                                                env1)
                                                             subprobs
                                                            in
                                                         FStar_Util.print1
                                                           "Adding subproblems for arguments: %s\n"
                                                           uu____15909
                                                       else ());
                                                      FStar_List.iter
                                                        (def_check_prob
                                                           "solve_t' subprobs")
                                                        subprobs;
                                                      (let formula =
                                                         let uu____15915 =
                                                           FStar_List.map
                                                             p_guard subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____15915
                                                          in
                                                       let wl4 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl3
                                                          in
                                                       let uu____15923 =
                                                         attempt subprobs wl4
                                                          in
                                                       solve env1 uu____15923))))
                                     | uu____15924 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___377_15960 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___377_15960.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___377_15960.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___377_15960.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___377_15960.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___377_15960.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___377_15960.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___377_15960.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___377_15960.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16035 = destruct_flex_t scrutinee wl1  in
             match uu____16035 with
             | ((_t,uv,_args),wl2) ->
                 let tc_annot env2 t =
                   let uu____16061 =
                     env2.FStar_TypeChecker_Env.type_of
                       (let uu___378_16069 = env2  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___378_16069.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___378_16069.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___378_16069.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___378_16069.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___378_16069.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___378_16069.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___378_16069.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___378_16069.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___378_16069.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___378_16069.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___378_16069.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___378_16069.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___378_16069.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___378_16069.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___378_16069.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___378_16069.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___378_16069.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___378_16069.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___378_16069.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___378_16069.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___378_16069.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___378_16069.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___378_16069.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___378_16069.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___378_16069.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___378_16069.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___378_16069.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___378_16069.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___378_16069.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts = true;
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___378_16069.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___378_16069.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___378_16069.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___378_16069.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___378_16069.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___378_16069.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___378_16069.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___378_16069.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___378_16069.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___378_16069.FStar_TypeChecker_Env.dep_graph);
                          FStar_TypeChecker_Env.nbe =
                            (uu___378_16069.FStar_TypeChecker_Env.nbe)
                        }) t
                      in
                   match uu____16061 with | (t1,uu____16075,g) -> (t1, g)  in
                 let uu____16077 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p
                     tc_annot
                    in
                 (match uu____16077 with
                  | (xs,pat_term,uu____16092,uu____16093) ->
                      let uu____16098 =
                        FStar_List.fold_left
                          (fun uu____16121  ->
                             fun x  ->
                               match uu____16121 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____16142 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____16142 with
                                    | (uu____16161,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____16098 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____16182 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____16182 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___379_16198 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___379_16198.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    tcenv = (uu___379_16198.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____16206 = solve env1 wl'  in
                                (match uu____16206 with
                                 | Success (uu____16209,imps) ->
                                     let wl'1 =
                                       let uu___380_16212 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___380_16212.wl_deferred);
                                         ctr = (uu___380_16212.ctr);
                                         defer_ok = (uu___380_16212.defer_ok);
                                         smt_ok = (uu___380_16212.smt_ok);
                                         tcenv = (uu___380_16212.tcenv);
                                         wl_implicits =
                                           (uu___380_16212.wl_implicits)
                                       }  in
                                     let uu____16213 = solve env1 wl'1  in
                                     (match uu____16213 with
                                      | Success (uu____16216,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___381_16220 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___381_16220.attempting);
                                                 wl_deferred =
                                                   (uu___381_16220.wl_deferred);
                                                 ctr = (uu___381_16220.ctr);
                                                 defer_ok =
                                                   (uu___381_16220.defer_ok);
                                                 smt_ok =
                                                   (uu___381_16220.smt_ok);
                                                 tcenv =
                                                   (uu___381_16220.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16221 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16227 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16248 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16248
                 then
                   let uu____16249 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16250 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16249 uu____16250
                 else ());
                (let uu____16252 =
                   let uu____16273 =
                     let uu____16282 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16282)  in
                   let uu____16289 =
                     let uu____16298 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16298)  in
                   (uu____16273, uu____16289)  in
                 match uu____16252 with
                 | ((uu____16327,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16330;
                                   FStar_Syntax_Syntax.vars = uu____16331;_}),
                    (s,t)) ->
                     let uu____16402 =
                       let uu____16403 = is_flex scrutinee  in
                       Prims.op_Negation uu____16403  in
                     if uu____16402
                     then
                       ((let uu____16411 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16411
                         then
                           let uu____16412 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16412
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16424 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16424
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16430 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16430
                           then
                             let uu____16431 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16432 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16431 uu____16432
                           else ());
                          (let pat_discriminates uu___340_16453 =
                             match uu___340_16453 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16468;
                                  FStar_Syntax_Syntax.p = uu____16469;_},FStar_Pervasives_Native.None
                                ,uu____16470) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16483;
                                  FStar_Syntax_Syntax.p = uu____16484;_},FStar_Pervasives_Native.None
                                ,uu____16485) -> true
                             | uu____16510 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16610 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16610 with
                                       | (uu____16611,uu____16612,t') ->
                                           let uu____16630 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____16630 with
                                            | (FullMatch ,uu____16641) ->
                                                true
                                            | (HeadMatch
                                               uu____16654,uu____16655) ->
                                                true
                                            | uu____16668 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16701 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16701
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16706 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16706 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16794,uu____16795) ->
                                       branches1
                                   | uu____16940 -> branches  in
                                 let uu____16995 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17004 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17004 with
                                        | (p,uu____17008,uu____17009) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____16995))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17065 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17065 with
                                | (p,uu____17073,e) ->
                                    ((let uu____17092 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17092
                                      then
                                        let uu____17093 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17094 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17093 uu____17094
                                      else ());
                                     (let uu____17096 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____17096)))))
                 | ((s,t),(uu____17111,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____17114;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17115;_}))
                     ->
                     let uu____17184 =
                       let uu____17185 = is_flex scrutinee  in
                       Prims.op_Negation uu____17185  in
                     if uu____17184
                     then
                       ((let uu____17193 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____17193
                         then
                           let uu____17194 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17194
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17206 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17206
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17212 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17212
                           then
                             let uu____17213 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____17214 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17213 uu____17214
                           else ());
                          (let pat_discriminates uu___340_17235 =
                             match uu___340_17235 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17250;
                                  FStar_Syntax_Syntax.p = uu____17251;_},FStar_Pervasives_Native.None
                                ,uu____17252) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17265;
                                  FStar_Syntax_Syntax.p = uu____17266;_},FStar_Pervasives_Native.None
                                ,uu____17267) -> true
                             | uu____17292 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17392 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17392 with
                                       | (uu____17393,uu____17394,t') ->
                                           let uu____17412 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____17412 with
                                            | (FullMatch ,uu____17423) ->
                                                true
                                            | (HeadMatch
                                               uu____17436,uu____17437) ->
                                                true
                                            | uu____17450 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17483 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17483
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17488 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17488 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17576,uu____17577) ->
                                       branches1
                                   | uu____17722 -> branches  in
                                 let uu____17777 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17786 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17786 with
                                        | (p,uu____17790,uu____17791) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17777))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17847 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17847 with
                                | (p,uu____17855,e) ->
                                    ((let uu____17874 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17874
                                      then
                                        let uu____17875 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17876 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17875 uu____17876
                                      else ());
                                     (let uu____17878 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17878)))))
                 | uu____17891 ->
                     ((let uu____17913 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17913
                       then
                         let uu____17914 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17915 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17914 uu____17915
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____17956 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____17956
            then
              let uu____17957 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17958 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____17959 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17960 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____17957 uu____17958 uu____17959 uu____17960
            else ());
           (let uu____17962 = head_matches_delta env1 t1 t2  in
            match uu____17962 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____17993,uu____17994) ->
                     let rec may_relate head3 =
                       let uu____18021 =
                         let uu____18022 = FStar_Syntax_Subst.compress head3
                            in
                         uu____18022.FStar_Syntax_Syntax.n  in
                       match uu____18021 with
                       | FStar_Syntax_Syntax.Tm_name uu____18025 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18026 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18049;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____18050;
                             FStar_Syntax_Syntax.fv_qual = uu____18051;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____18054;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____18055;
                             FStar_Syntax_Syntax.fv_qual = uu____18056;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____18060,uu____18061) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____18103) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____18109) ->
                           may_relate t
                       | uu____18114 -> false  in
                     let uu____18115 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____18115 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____18130 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____18130
                          then
                            let uu____18131 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____18131 with
                             | (guard,wl2) ->
                                 let uu____18138 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____18138)
                          else
                            (let uu____18140 =
                               let uu____18141 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____18142 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               FStar_Util.format2 "head mismatch (%s vs %s)"
                                 uu____18141 uu____18142
                                in
                             giveup env1 uu____18140 orig))
                 | (HeadMatch (true ),uu____18143) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18156 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____18156 with
                        | (guard,wl2) ->
                            let uu____18163 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____18163)
                     else
                       (let uu____18165 =
                          let uu____18166 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____18167 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____18166 uu____18167
                           in
                        giveup env1 uu____18165 orig)
                 | (uu____18168,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___382_18182 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___382_18182.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___382_18182.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___382_18182.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___382_18182.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___382_18182.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___382_18182.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___382_18182.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___382_18182.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18206 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18206
          then
            let uu____18207 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18207
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18212 =
                let uu____18215 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18215  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18212 t1);
             (let uu____18233 =
                let uu____18236 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18236  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18233 t2);
             (let uu____18254 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18254
              then
                let uu____18255 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18256 =
                  let uu____18257 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18258 =
                    let uu____18259 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18259  in
                  Prims.strcat uu____18257 uu____18258  in
                let uu____18260 =
                  let uu____18261 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18262 =
                    let uu____18263 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18263  in
                  Prims.strcat uu____18261 uu____18262  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18255
                  uu____18256 uu____18260
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18266,uu____18267) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18290,FStar_Syntax_Syntax.Tm_delayed uu____18291) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18314,uu____18315) ->
                  let uu____18342 =
                    let uu___383_18343 = problem  in
                    let uu____18344 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___383_18343.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18344;
                      FStar_TypeChecker_Common.relation =
                        (uu___383_18343.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___383_18343.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___383_18343.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___383_18343.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___383_18343.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___383_18343.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___383_18343.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___383_18343.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18342 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18345,uu____18346) ->
                  let uu____18353 =
                    let uu___384_18354 = problem  in
                    let uu____18355 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___384_18354.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18355;
                      FStar_TypeChecker_Common.relation =
                        (uu___384_18354.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___384_18354.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___384_18354.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___384_18354.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___384_18354.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___384_18354.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___384_18354.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___384_18354.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18353 wl
              | (uu____18356,FStar_Syntax_Syntax.Tm_ascribed uu____18357) ->
                  let uu____18384 =
                    let uu___385_18385 = problem  in
                    let uu____18386 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___385_18385.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___385_18385.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___385_18385.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18386;
                      FStar_TypeChecker_Common.element =
                        (uu___385_18385.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___385_18385.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___385_18385.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___385_18385.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___385_18385.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___385_18385.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18384 wl
              | (uu____18387,FStar_Syntax_Syntax.Tm_meta uu____18388) ->
                  let uu____18395 =
                    let uu___386_18396 = problem  in
                    let uu____18397 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___386_18396.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___386_18396.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___386_18396.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18397;
                      FStar_TypeChecker_Common.element =
                        (uu___386_18396.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___386_18396.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___386_18396.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___386_18396.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___386_18396.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___386_18396.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18395 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18399),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18401)) ->
                  let uu____18410 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18410
              | (FStar_Syntax_Syntax.Tm_bvar uu____18411,uu____18412) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18413,FStar_Syntax_Syntax.Tm_bvar uu____18414) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___341_18483 =
                    match uu___341_18483 with
                    | [] -> c
                    | bs ->
                        let uu____18511 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18511
                     in
                  let uu____18522 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18522 with
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
                                    let uu____18671 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18671
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
                  let mk_t t l uu___342_18756 =
                    match uu___342_18756 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18798 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18798 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____18943 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____18944 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____18943
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____18944 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____18945,uu____18946) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18975 -> true
                    | uu____18994 -> false  in
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
                      (let uu____19047 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_19055 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_19055.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_19055.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_19055.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_19055.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_19055.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_19055.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_19055.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_19055.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_19055.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_19055.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_19055.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_19055.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_19055.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_19055.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_19055.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_19055.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_19055.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_19055.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_19055.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_19055.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_19055.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_19055.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_19055.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_19055.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_19055.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_19055.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_19055.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_19055.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_19055.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_19055.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_19055.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_19055.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_19055.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_19055.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_19055.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_19055.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_19055.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___387_19055.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_19055.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19047 with
                       | (uu____19058,ty,uu____19060) ->
                           let uu____19061 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19061)
                     in
                  let uu____19062 =
                    let uu____19079 = maybe_eta t1  in
                    let uu____19086 = maybe_eta t2  in
                    (uu____19079, uu____19086)  in
                  (match uu____19062 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_19128 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_19128.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_19128.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_19128.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_19128.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_19128.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_19128.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_19128.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_19128.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19149 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19149
                       then
                         let uu____19150 = destruct_flex_t not_abs wl  in
                         (match uu____19150 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19165 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19165.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19165.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19165.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19165.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19165.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19165.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19165.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19165.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19187 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19187
                       then
                         let uu____19188 = destruct_flex_t not_abs wl  in
                         (match uu____19188 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19203 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19203.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19203.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19203.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19203.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19203.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19203.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19203.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19203.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19205 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19222,FStar_Syntax_Syntax.Tm_abs uu____19223) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19252 -> true
                    | uu____19271 -> false  in
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
                      (let uu____19324 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___387_19332 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_19332.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_19332.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_19332.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_19332.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_19332.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_19332.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_19332.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_19332.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_19332.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_19332.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_19332.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_19332.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_19332.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_19332.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_19332.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_19332.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_19332.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_19332.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_19332.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_19332.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_19332.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_19332.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_19332.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_19332.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_19332.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_19332.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_19332.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_19332.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_19332.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_19332.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_19332.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_19332.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_19332.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_19332.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_19332.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_19332.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_19332.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___387_19332.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___387_19332.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19324 with
                       | (uu____19335,ty,uu____19337) ->
                           let uu____19338 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19338)
                     in
                  let uu____19339 =
                    let uu____19356 = maybe_eta t1  in
                    let uu____19363 = maybe_eta t2  in
                    (uu____19356, uu____19363)  in
                  (match uu____19339 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___388_19405 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___388_19405.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___388_19405.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___388_19405.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___388_19405.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___388_19405.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___388_19405.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___388_19405.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___388_19405.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19426 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19426
                       then
                         let uu____19427 = destruct_flex_t not_abs wl  in
                         (match uu____19427 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19442 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19442.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19442.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19442.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19442.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19442.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19442.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19442.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19442.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19464 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19464
                       then
                         let uu____19465 = destruct_flex_t not_abs wl  in
                         (match uu____19465 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___389_19480 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___389_19480.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___389_19480.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___389_19480.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___389_19480.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___389_19480.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___389_19480.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___389_19480.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___389_19480.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19482 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19511 =
                    let uu____19516 =
                      head_matches_delta env x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19516 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___390_19544 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19544.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19544.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19546 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19546.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19546.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19547,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___390_19561 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___390_19561.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___390_19561.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___391_19563 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___391_19563.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___391_19563.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19564 -> (x1, x2)  in
                  (match uu____19511 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19583 = as_refinement false env t11  in
                       (match uu____19583 with
                        | (x12,phi11) ->
                            let uu____19590 = as_refinement false env t21  in
                            (match uu____19590 with
                             | (x22,phi21) ->
                                 ((let uu____19598 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19598
                                   then
                                     ((let uu____19600 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19601 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19602 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19600
                                         uu____19601 uu____19602);
                                      (let uu____19603 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19604 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19605 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19603
                                         uu____19604 uu____19605))
                                   else ());
                                  (let uu____19607 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19607 with
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
                                         let uu____19675 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19675
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19687 =
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
                                         (let uu____19698 =
                                            let uu____19701 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19701
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19698
                                            (p_guard base_prob));
                                         (let uu____19719 =
                                            let uu____19722 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19722
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19719
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19740 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19740)
                                          in
                                       let has_uvars =
                                         (let uu____19744 =
                                            let uu____19745 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19745
                                             in
                                          Prims.op_Negation uu____19744) ||
                                           (let uu____19749 =
                                              let uu____19750 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19750
                                               in
                                            Prims.op_Negation uu____19749)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19753 =
                                           let uu____19758 =
                                             let uu____19767 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19767]  in
                                           mk_t_problem wl1 uu____19758 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19753 with
                                          | (ref_prob,wl2) ->
                                              let uu____19788 =
                                                solve env1
                                                  (let uu___392_19790 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___392_19790.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___392_19790.smt_ok);
                                                     tcenv =
                                                       (uu___392_19790.tcenv);
                                                     wl_implicits =
                                                       (uu___392_19790.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19788 with
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
                                               | Success uu____19800 ->
                                                   let guard =
                                                     let uu____19808 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19808
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___393_19817 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___393_19817.attempting);
                                                       wl_deferred =
                                                         (uu___393_19817.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___393_19817.defer_ok);
                                                       smt_ok =
                                                         (uu___393_19817.smt_ok);
                                                       tcenv =
                                                         (uu___393_19817.tcenv);
                                                       wl_implicits =
                                                         (uu___393_19817.wl_implicits)
                                                     }  in
                                                   let uu____19818 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19818))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19820,FStar_Syntax_Syntax.Tm_uvar uu____19821) ->
                  let uu____19846 = destruct_flex_t t1 wl  in
                  (match uu____19846 with
                   | (f1,wl1) ->
                       let uu____19853 = destruct_flex_t t2 wl1  in
                       (match uu____19853 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19860;
                    FStar_Syntax_Syntax.pos = uu____19861;
                    FStar_Syntax_Syntax.vars = uu____19862;_},uu____19863),FStar_Syntax_Syntax.Tm_uvar
                 uu____19864) ->
                  let uu____19913 = destruct_flex_t t1 wl  in
                  (match uu____19913 with
                   | (f1,wl1) ->
                       let uu____19920 = destruct_flex_t t2 wl1  in
                       (match uu____19920 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19927,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19928;
                    FStar_Syntax_Syntax.pos = uu____19929;
                    FStar_Syntax_Syntax.vars = uu____19930;_},uu____19931))
                  ->
                  let uu____19980 = destruct_flex_t t1 wl  in
                  (match uu____19980 with
                   | (f1,wl1) ->
                       let uu____19987 = destruct_flex_t t2 wl1  in
                       (match uu____19987 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19994;
                    FStar_Syntax_Syntax.pos = uu____19995;
                    FStar_Syntax_Syntax.vars = uu____19996;_},uu____19997),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19998;
                    FStar_Syntax_Syntax.pos = uu____19999;
                    FStar_Syntax_Syntax.vars = uu____20000;_},uu____20001))
                  ->
                  let uu____20074 = destruct_flex_t t1 wl  in
                  (match uu____20074 with
                   | (f1,wl1) ->
                       let uu____20081 = destruct_flex_t t2 wl1  in
                       (match uu____20081 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20088,uu____20089) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20102 = destruct_flex_t t1 wl  in
                  (match uu____20102 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20109;
                    FStar_Syntax_Syntax.pos = uu____20110;
                    FStar_Syntax_Syntax.vars = uu____20111;_},uu____20112),uu____20113)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20150 = destruct_flex_t t1 wl  in
                  (match uu____20150 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____20157,FStar_Syntax_Syntax.Tm_uvar uu____20158) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____20171,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20172;
                    FStar_Syntax_Syntax.pos = uu____20173;
                    FStar_Syntax_Syntax.vars = uu____20174;_},uu____20175))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20212,FStar_Syntax_Syntax.Tm_arrow uu____20213) ->
                  solve_t' env
                    (let uu___394_20241 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20241.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20241.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20241.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20241.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20241.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20241.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20241.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20241.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20241.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20242;
                    FStar_Syntax_Syntax.pos = uu____20243;
                    FStar_Syntax_Syntax.vars = uu____20244;_},uu____20245),FStar_Syntax_Syntax.Tm_arrow
                 uu____20246) ->
                  solve_t' env
                    (let uu___394_20298 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___394_20298.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___394_20298.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___394_20298.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___394_20298.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___394_20298.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___394_20298.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___394_20298.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___394_20298.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___394_20298.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20299,FStar_Syntax_Syntax.Tm_uvar uu____20300) ->
                  let uu____20313 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20313
              | (uu____20314,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20315;
                    FStar_Syntax_Syntax.pos = uu____20316;
                    FStar_Syntax_Syntax.vars = uu____20317;_},uu____20318))
                  ->
                  let uu____20355 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20355
              | (FStar_Syntax_Syntax.Tm_uvar uu____20356,uu____20357) ->
                  let uu____20370 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20370
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20371;
                    FStar_Syntax_Syntax.pos = uu____20372;
                    FStar_Syntax_Syntax.vars = uu____20373;_},uu____20374),uu____20375)
                  ->
                  let uu____20412 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20412
              | (FStar_Syntax_Syntax.Tm_refine uu____20413,uu____20414) ->
                  let t21 =
                    let uu____20422 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20422  in
                  solve_t env
                    (let uu___395_20448 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___395_20448.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___395_20448.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___395_20448.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___395_20448.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___395_20448.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___395_20448.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___395_20448.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___395_20448.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___395_20448.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20449,FStar_Syntax_Syntax.Tm_refine uu____20450) ->
                  let t11 =
                    let uu____20458 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20458  in
                  solve_t env
                    (let uu___396_20484 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___396_20484.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___396_20484.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___396_20484.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___396_20484.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___396_20484.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___396_20484.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___396_20484.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___396_20484.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___396_20484.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20566 =
                    let uu____20567 = guard_of_prob env wl problem t1 t2  in
                    match uu____20567 with
                    | (guard,wl1) ->
                        let uu____20574 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20574
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20785 = br1  in
                        (match uu____20785 with
                         | (p1,w1,uu____20810) ->
                             let uu____20827 = br2  in
                             (match uu____20827 with
                              | (p2,w2,uu____20846) ->
                                  let uu____20851 =
                                    let uu____20852 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20852  in
                                  if uu____20851
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20868 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20868 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____20901 = br2  in
                                         (match uu____20901 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____20938 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____20938
                                                 in
                                              let uu____20951 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____20974,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____20991) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____21034 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____21034 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____20951
                                                (fun uu____21076  ->
                                                   match uu____21076 with
                                                   | (wprobs,wl2) ->
                                                       let uu____21097 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____21097
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____21112 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____21112
                                                              (fun
                                                                 uu____21136 
                                                                 ->
                                                                 match uu____21136
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____21221 -> FStar_Pervasives_Native.None  in
                  let uu____21258 = solve_branches wl brs1 brs2  in
                  (match uu____21258 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21286 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21286 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____21305 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21305  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21314 =
                              let uu____21315 =
                                attempt sub_probs1
                                  (let uu___397_21317 = wl3  in
                                   {
                                     attempting = (uu___397_21317.attempting);
                                     wl_deferred =
                                       (uu___397_21317.wl_deferred);
                                     ctr = (uu___397_21317.ctr);
                                     defer_ok = (uu___397_21317.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___397_21317.tcenv);
                                     wl_implicits =
                                       (uu___397_21317.wl_implicits)
                                   })
                                 in
                              solve env uu____21315  in
                            (match uu____21314 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21321 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21327,uu____21328) ->
                  let head1 =
                    let uu____21352 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21352
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21398 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21398
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21444 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21444
                    then
                      let uu____21445 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21446 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21447 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21445 uu____21446 uu____21447
                    else ());
                   (let no_free_uvars t =
                      (let uu____21457 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21457) &&
                        (let uu____21461 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21461)
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
                      let uu____21477 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21477 = FStar_Syntax_Util.Equal  in
                    let uu____21478 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21478
                    then
                      let uu____21479 =
                        let uu____21486 = equal t1 t2  in
                        if uu____21486
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21496 = mk_eq2 wl orig t1 t2  in
                           match uu____21496 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21479 with
                      | (guard,wl1) ->
                          let uu____21517 = solve_prob orig guard [] wl1  in
                          solve env uu____21517
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21519,uu____21520) ->
                  let head1 =
                    let uu____21528 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21528
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21574 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21574
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21620 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21620
                    then
                      let uu____21621 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21622 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21623 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21621 uu____21622 uu____21623
                    else ());
                   (let no_free_uvars t =
                      (let uu____21633 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21633) &&
                        (let uu____21637 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21637)
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
                      let uu____21653 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21653 = FStar_Syntax_Util.Equal  in
                    let uu____21654 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21654
                    then
                      let uu____21655 =
                        let uu____21662 = equal t1 t2  in
                        if uu____21662
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21672 = mk_eq2 wl orig t1 t2  in
                           match uu____21672 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21655 with
                      | (guard,wl1) ->
                          let uu____21693 = solve_prob orig guard [] wl1  in
                          solve env uu____21693
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____21695,uu____21696) ->
                  let head1 =
                    let uu____21698 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21698
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21744 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21744
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21790 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21790
                    then
                      let uu____21791 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21792 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21793 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21791 uu____21792 uu____21793
                    else ());
                   (let no_free_uvars t =
                      (let uu____21803 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21803) &&
                        (let uu____21807 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21807)
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
                      let uu____21823 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21823 = FStar_Syntax_Util.Equal  in
                    let uu____21824 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21824
                    then
                      let uu____21825 =
                        let uu____21832 = equal t1 t2  in
                        if uu____21832
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21842 = mk_eq2 wl orig t1 t2  in
                           match uu____21842 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21825 with
                      | (guard,wl1) ->
                          let uu____21863 = solve_prob orig guard [] wl1  in
                          solve env uu____21863
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____21865,uu____21866) ->
                  let head1 =
                    let uu____21868 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21868
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21914 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21914
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21960 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21960
                    then
                      let uu____21961 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21962 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21963 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21961 uu____21962 uu____21963
                    else ());
                   (let no_free_uvars t =
                      (let uu____21973 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21973) &&
                        (let uu____21977 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21977)
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
                      let uu____21993 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21993 = FStar_Syntax_Util.Equal  in
                    let uu____21994 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21994
                    then
                      let uu____21995 =
                        let uu____22002 = equal t1 t2  in
                        if uu____22002
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22012 = mk_eq2 wl orig t1 t2  in
                           match uu____22012 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21995 with
                      | (guard,wl1) ->
                          let uu____22033 = solve_prob orig guard [] wl1  in
                          solve env uu____22033
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____22035,uu____22036) ->
                  let head1 =
                    let uu____22038 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22038
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22084 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22084
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22130 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22130
                    then
                      let uu____22131 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22132 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22133 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22131 uu____22132 uu____22133
                    else ());
                   (let no_free_uvars t =
                      (let uu____22143 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22143) &&
                        (let uu____22147 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22147)
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
                      let uu____22163 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22163 = FStar_Syntax_Util.Equal  in
                    let uu____22164 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22164
                    then
                      let uu____22165 =
                        let uu____22172 = equal t1 t2  in
                        if uu____22172
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22182 = mk_eq2 wl orig t1 t2  in
                           match uu____22182 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22165 with
                      | (guard,wl1) ->
                          let uu____22203 = solve_prob orig guard [] wl1  in
                          solve env uu____22203
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22205,uu____22206) ->
                  let head1 =
                    let uu____22224 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22224
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22270 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22270
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22316 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22316
                    then
                      let uu____22317 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22318 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22319 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22317 uu____22318 uu____22319
                    else ());
                   (let no_free_uvars t =
                      (let uu____22329 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22329) &&
                        (let uu____22333 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22333)
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
                      let uu____22349 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22349 = FStar_Syntax_Util.Equal  in
                    let uu____22350 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22350
                    then
                      let uu____22351 =
                        let uu____22358 = equal t1 t2  in
                        if uu____22358
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22368 = mk_eq2 wl orig t1 t2  in
                           match uu____22368 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22351 with
                      | (guard,wl1) ->
                          let uu____22389 = solve_prob orig guard [] wl1  in
                          solve env uu____22389
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22391,FStar_Syntax_Syntax.Tm_match uu____22392) ->
                  let head1 =
                    let uu____22416 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22416
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22462 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22462
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22508 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22508
                    then
                      let uu____22509 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22510 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22511 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22509 uu____22510 uu____22511
                    else ());
                   (let no_free_uvars t =
                      (let uu____22521 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22521) &&
                        (let uu____22525 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22525)
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
                      let uu____22541 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22541 = FStar_Syntax_Util.Equal  in
                    let uu____22542 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22542
                    then
                      let uu____22543 =
                        let uu____22550 = equal t1 t2  in
                        if uu____22550
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22560 = mk_eq2 wl orig t1 t2  in
                           match uu____22560 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22543 with
                      | (guard,wl1) ->
                          let uu____22581 = solve_prob orig guard [] wl1  in
                          solve env uu____22581
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22583,FStar_Syntax_Syntax.Tm_uinst uu____22584) ->
                  let head1 =
                    let uu____22592 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22592
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22632 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22632
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22672 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22672
                    then
                      let uu____22673 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22674 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22675 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22673 uu____22674 uu____22675
                    else ());
                   (let no_free_uvars t =
                      (let uu____22685 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22685) &&
                        (let uu____22689 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22689)
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
                      let uu____22705 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22705 = FStar_Syntax_Util.Equal  in
                    let uu____22706 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22706
                    then
                      let uu____22707 =
                        let uu____22714 = equal t1 t2  in
                        if uu____22714
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22724 = mk_eq2 wl orig t1 t2  in
                           match uu____22724 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22707 with
                      | (guard,wl1) ->
                          let uu____22745 = solve_prob orig guard [] wl1  in
                          solve env uu____22745
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22747,FStar_Syntax_Syntax.Tm_name uu____22748) ->
                  let head1 =
                    let uu____22750 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22750
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22790 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22790
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22830 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22830
                    then
                      let uu____22831 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22832 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22833 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22831 uu____22832 uu____22833
                    else ());
                   (let no_free_uvars t =
                      (let uu____22843 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22843) &&
                        (let uu____22847 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22847)
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
                      let uu____22863 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22863 = FStar_Syntax_Util.Equal  in
                    let uu____22864 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22864
                    then
                      let uu____22865 =
                        let uu____22872 = equal t1 t2  in
                        if uu____22872
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22882 = mk_eq2 wl orig t1 t2  in
                           match uu____22882 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22865 with
                      | (guard,wl1) ->
                          let uu____22903 = solve_prob orig guard [] wl1  in
                          solve env uu____22903
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____22905,FStar_Syntax_Syntax.Tm_constant uu____22906) ->
                  let head1 =
                    let uu____22908 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22908
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22948 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22948
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22988 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22988
                    then
                      let uu____22989 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22990 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22991 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22989 uu____22990 uu____22991
                    else ());
                   (let no_free_uvars t =
                      (let uu____23001 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23001) &&
                        (let uu____23005 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23005)
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
                      let uu____23021 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23021 = FStar_Syntax_Util.Equal  in
                    let uu____23022 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23022
                    then
                      let uu____23023 =
                        let uu____23030 = equal t1 t2  in
                        if uu____23030
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23040 = mk_eq2 wl orig t1 t2  in
                           match uu____23040 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23023 with
                      | (guard,wl1) ->
                          let uu____23061 = solve_prob orig guard [] wl1  in
                          solve env uu____23061
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23063,FStar_Syntax_Syntax.Tm_fvar uu____23064) ->
                  let head1 =
                    let uu____23066 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23066
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23112 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23112
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23158 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23158
                    then
                      let uu____23159 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23160 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23161 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23159 uu____23160 uu____23161
                    else ());
                   (let no_free_uvars t =
                      (let uu____23171 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23171) &&
                        (let uu____23175 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23175)
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
                      let uu____23191 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23191 = FStar_Syntax_Util.Equal  in
                    let uu____23192 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23192
                    then
                      let uu____23193 =
                        let uu____23200 = equal t1 t2  in
                        if uu____23200
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23210 = mk_eq2 wl orig t1 t2  in
                           match uu____23210 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23193 with
                      | (guard,wl1) ->
                          let uu____23231 = solve_prob orig guard [] wl1  in
                          solve env uu____23231
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____23233,FStar_Syntax_Syntax.Tm_app uu____23234) ->
                  let head1 =
                    let uu____23252 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23252
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23292 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23292
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23332 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23332
                    then
                      let uu____23333 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23334 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23335 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23333 uu____23334 uu____23335
                    else ());
                   (let no_free_uvars t =
                      (let uu____23345 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23345) &&
                        (let uu____23349 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23349)
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
                      let uu____23365 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23365 = FStar_Syntax_Util.Equal  in
                    let uu____23366 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23366
                    then
                      let uu____23367 =
                        let uu____23374 = equal t1 t2  in
                        if uu____23374
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23384 = mk_eq2 wl orig t1 t2  in
                           match uu____23384 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23367 with
                      | (guard,wl1) ->
                          let uu____23405 = solve_prob orig guard [] wl1  in
                          solve env uu____23405
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23407,FStar_Syntax_Syntax.Tm_let uu____23408) ->
                  let uu____23433 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23433
                  then
                    let uu____23434 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23434
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23436,uu____23437) ->
                  let uu____23450 =
                    let uu____23455 =
                      let uu____23456 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23457 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23458 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23459 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23456 uu____23457 uu____23458 uu____23459
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23455)
                     in
                  FStar_Errors.raise_error uu____23450
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23460,FStar_Syntax_Syntax.Tm_let uu____23461) ->
                  let uu____23474 =
                    let uu____23479 =
                      let uu____23480 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23481 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23482 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23483 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23480 uu____23481 uu____23482 uu____23483
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23479)
                     in
                  FStar_Errors.raise_error uu____23474
                    t1.FStar_Syntax_Syntax.pos
              | uu____23484 -> giveup env "head tag mismatch" orig))))

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
          (let uu____23545 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23545
           then
             let uu____23546 =
               let uu____23547 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23547  in
             let uu____23548 =
               let uu____23549 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23549  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23546 uu____23548
           else ());
          (let uu____23551 =
             let uu____23552 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23552  in
           if uu____23551
           then
             let uu____23553 =
               let uu____23554 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23555 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23554 uu____23555
                in
             giveup env uu____23553 orig
           else
             (let uu____23557 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23557 with
              | (ret_sub_prob,wl1) ->
                  let uu____23564 =
                    FStar_List.fold_right2
                      (fun uu____23601  ->
                         fun uu____23602  ->
                           fun uu____23603  ->
                             match (uu____23601, uu____23602, uu____23603)
                             with
                             | ((a1,uu____23647),(a2,uu____23649),(arg_sub_probs,wl2))
                                 ->
                                 let uu____23682 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____23682 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23564 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____23711 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____23711  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____23719 = attempt sub_probs wl3  in
                       solve env uu____23719)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23742 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23745)::[] -> wp1
              | uu____23770 ->
                  let uu____23781 =
                    let uu____23782 =
                      let uu____23783 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23783  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23782
                     in
                  failwith uu____23781
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23789 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23789]
              | x -> x  in
            let uu____23791 =
              let uu____23802 =
                let uu____23811 =
                  let uu____23812 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23812 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23811  in
              [uu____23802]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23791;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23829 = lift_c1 ()  in solve_eq uu____23829 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___343_23835  ->
                       match uu___343_23835 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23836 -> false))
                in
             let uu____23837 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23867)::uu____23868,(wp2,uu____23870)::uu____23871)
                   -> (wp1, wp2)
               | uu____23944 ->
                   let uu____23969 =
                     let uu____23974 =
                       let uu____23975 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____23976 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____23975 uu____23976
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____23974)
                      in
                   FStar_Errors.raise_error uu____23969
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23837 with
             | (wpc1,wpc2) ->
                 let uu____23983 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____23983
                 then
                   let uu____23986 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____23986 wl
                 else
                   (let uu____23988 =
                      let uu____23995 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____23995  in
                    match uu____23988 with
                    | (c2_decl,qualifiers) ->
                        let uu____24016 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____24016
                        then
                          let c1_repr =
                            let uu____24020 =
                              let uu____24021 =
                                let uu____24022 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____24022  in
                              let uu____24023 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24021 uu____24023
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24020
                             in
                          let c2_repr =
                            let uu____24025 =
                              let uu____24026 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____24027 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24026 uu____24027
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24025
                             in
                          let uu____24028 =
                            let uu____24033 =
                              let uu____24034 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____24035 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____24034 uu____24035
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____24033
                             in
                          (match uu____24028 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____24039 = attempt [prob] wl2  in
                               solve env uu____24039)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____24050 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24050
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____24053 =
                                     let uu____24060 =
                                       let uu____24061 =
                                         let uu____24078 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____24081 =
                                           let uu____24092 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____24101 =
                                             let uu____24112 =
                                               let uu____24121 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____24121
                                                in
                                             [uu____24112]  in
                                           uu____24092 :: uu____24101  in
                                         (uu____24078, uu____24081)  in
                                       FStar_Syntax_Syntax.Tm_app uu____24061
                                        in
                                     FStar_Syntax_Syntax.mk uu____24060  in
                                   uu____24053 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____24172 =
                                    let uu____24179 =
                                      let uu____24180 =
                                        let uu____24197 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____24200 =
                                          let uu____24211 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24220 =
                                            let uu____24231 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24240 =
                                              let uu____24251 =
                                                let uu____24260 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24260
                                                 in
                                              [uu____24251]  in
                                            uu____24231 :: uu____24240  in
                                          uu____24211 :: uu____24220  in
                                        (uu____24197, uu____24200)  in
                                      FStar_Syntax_Syntax.Tm_app uu____24180
                                       in
                                    FStar_Syntax_Syntax.mk uu____24179  in
                                  uu____24172 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24317 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24317
                            then
                              let uu____24318 =
                                let uu____24319 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24319
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24318
                            else ());
                           (let uu____24321 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24321 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24329 =
                                    let uu____24332 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24332
                                     in
                                  solve_prob orig uu____24329 [] wl1  in
                                let uu____24335 = attempt [base_prob] wl2  in
                                solve env uu____24335))))
           in
        let uu____24336 = FStar_Util.physical_equality c1 c2  in
        if uu____24336
        then
          let uu____24337 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24337
        else
          ((let uu____24340 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24340
            then
              let uu____24341 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24342 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24341
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24342
            else ());
           (let uu____24344 =
              let uu____24353 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24356 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24353, uu____24356)  in
            match uu____24344 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24374),FStar_Syntax_Syntax.Total
                    (t2,uu____24376)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24393 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24393 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24394,FStar_Syntax_Syntax.Total uu____24395) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24413),FStar_Syntax_Syntax.Total
                    (t2,uu____24415)) ->
                     let uu____24432 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24432 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24434),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24436)) ->
                     let uu____24453 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24453 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24455),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24457)) ->
                     let uu____24474 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24474 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24475,FStar_Syntax_Syntax.Comp uu____24476) ->
                     let uu____24485 =
                       let uu___398_24488 = problem  in
                       let uu____24491 =
                         let uu____24492 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24492
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24488.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24491;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24488.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24488.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24488.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24488.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24488.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24488.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24488.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24488.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24485 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24493,FStar_Syntax_Syntax.Comp uu____24494) ->
                     let uu____24503 =
                       let uu___398_24506 = problem  in
                       let uu____24509 =
                         let uu____24510 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24510
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___398_24506.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24509;
                         FStar_TypeChecker_Common.relation =
                           (uu___398_24506.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___398_24506.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___398_24506.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___398_24506.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___398_24506.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___398_24506.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___398_24506.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___398_24506.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24503 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24511,FStar_Syntax_Syntax.GTotal uu____24512) ->
                     let uu____24521 =
                       let uu___399_24524 = problem  in
                       let uu____24527 =
                         let uu____24528 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24528
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24524.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24524.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24524.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24527;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24524.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24524.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24524.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24524.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24524.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24524.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24521 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24529,FStar_Syntax_Syntax.Total uu____24530) ->
                     let uu____24539 =
                       let uu___399_24542 = problem  in
                       let uu____24545 =
                         let uu____24546 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24546
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___399_24542.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___399_24542.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___399_24542.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24545;
                         FStar_TypeChecker_Common.element =
                           (uu___399_24542.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___399_24542.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___399_24542.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___399_24542.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___399_24542.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___399_24542.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24539 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24547,FStar_Syntax_Syntax.Comp uu____24548) ->
                     let uu____24549 =
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
                     if uu____24549
                     then
                       let uu____24550 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24550 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24554 =
                            let uu____24559 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24559
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24565 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24566 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24565, uu____24566))
                             in
                          match uu____24554 with
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
                           (let uu____24573 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24573
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24575 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24575 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24578 =
                                  let uu____24579 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24580 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24579 uu____24580
                                   in
                                giveup env uu____24578 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24587 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24587 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24628 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24628 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24646 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24674  ->
                match uu____24674 with
                | (u1,u2) ->
                    let uu____24681 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24682 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24681 uu____24682))
         in
      FStar_All.pipe_right uu____24646 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24709,[])) -> "{}"
      | uu____24734 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24757 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____24757
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24760 =
              FStar_List.map
                (fun uu____24770  ->
                   match uu____24770 with
                   | (uu____24775,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24760 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24780 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24780 imps
  
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
                  let uu____24833 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____24833
                  then
                    let uu____24834 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____24835 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24834
                      (rel_to_string rel) uu____24835
                  else "TOP"  in
                let uu____24837 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____24837 with
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
              let uu____24895 =
                let uu____24898 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____24898
                 in
              FStar_Syntax_Syntax.new_bv uu____24895 t1  in
            let uu____24901 =
              let uu____24906 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____24906
               in
            match uu____24901 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____24979 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____24979
              then
                let uu____24980 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____24980
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
          ((let uu____25002 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____25002
            then
              let uu____25003 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____25003
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____25007 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____25007
             then
               let uu____25008 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____25008
             else ());
            (let f2 =
               let uu____25011 =
                 let uu____25012 = FStar_Syntax_Util.unmeta f1  in
                 uu____25012.FStar_Syntax_Syntax.n  in
               match uu____25011 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____25016 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___400_25017 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___400_25017.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___400_25017.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___400_25017.FStar_TypeChecker_Env.implicits)
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
            let uu____25071 =
              let uu____25072 =
                let uu____25073 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____25073;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____25072  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____25071
  
let with_guard_no_simp :
  'Auu____25088 .
    'Auu____25088 ->
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
            let uu____25111 =
              let uu____25112 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____25112;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____25111
  
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
          (let uu____25142 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____25142
           then
             let uu____25143 = FStar_Syntax_Print.term_to_string t1  in
             let uu____25144 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____25143
               uu____25144
           else ());
          (let uu____25146 =
             let uu____25151 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____25151
              in
           match uu____25146 with
           | (prob,wl) ->
               let g =
                 let uu____25159 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____25169  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____25159  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25203 = try_teq true env t1 t2  in
        match uu____25203 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25207 = FStar_TypeChecker_Env.get_range env  in
              let uu____25208 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25207 uu____25208);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25215 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25215
              then
                let uu____25216 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25217 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25218 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25216
                  uu____25217 uu____25218
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
          let uu____25240 = FStar_TypeChecker_Env.get_range env  in
          let uu____25241 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25240 uu____25241
  
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
        (let uu____25266 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25266
         then
           let uu____25267 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25268 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25267 uu____25268
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25271 =
           let uu____25278 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25278 "sub_comp"
            in
         match uu____25271 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25289 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25299  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25289)))
  
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
      fun uu____25344  ->
        match uu____25344 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25387 =
                 let uu____25392 =
                   let uu____25393 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25394 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25393 uu____25394
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25392)  in
               let uu____25395 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25387 uu____25395)
               in
            let equiv1 v1 v' =
              let uu____25407 =
                let uu____25412 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25413 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25412, uu____25413)  in
              match uu____25407 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25432 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25462 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25462 with
                      | FStar_Syntax_Syntax.U_unif uu____25469 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25498  ->
                                    match uu____25498 with
                                    | (u,v') ->
                                        let uu____25507 = equiv1 v1 v'  in
                                        if uu____25507
                                        then
                                          let uu____25510 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25510 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25526 -> []))
               in
            let uu____25531 =
              let wl =
                let uu___401_25535 = empty_worklist env  in
                {
                  attempting = (uu___401_25535.attempting);
                  wl_deferred = (uu___401_25535.wl_deferred);
                  ctr = (uu___401_25535.ctr);
                  defer_ok = false;
                  smt_ok = (uu___401_25535.smt_ok);
                  tcenv = (uu___401_25535.tcenv);
                  wl_implicits = (uu___401_25535.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25553  ->
                      match uu____25553 with
                      | (lb,v1) ->
                          let uu____25560 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25560 with
                           | USolved wl1 -> ()
                           | uu____25562 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25572 =
              match uu____25572 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25581) -> true
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
                      uu____25604,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25606,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25617) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25624,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25632 -> false)
               in
            let uu____25637 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25652  ->
                      match uu____25652 with
                      | (u,v1) ->
                          let uu____25659 = check_ineq (u, v1)  in
                          if uu____25659
                          then true
                          else
                            ((let uu____25662 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____25662
                              then
                                let uu____25663 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____25664 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____25663
                                  uu____25664
                              else ());
                             false)))
               in
            if uu____25637
            then ()
            else
              ((let uu____25668 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25668
                then
                  ((let uu____25670 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25670);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25680 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25680))
                else ());
               (let uu____25690 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25690))
  
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
        let fail1 uu____25757 =
          match uu____25757 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___402_25778 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___402_25778.attempting);
            wl_deferred = (uu___402_25778.wl_deferred);
            ctr = (uu___402_25778.ctr);
            defer_ok;
            smt_ok = (uu___402_25778.smt_ok);
            tcenv = (uu___402_25778.tcenv);
            wl_implicits = (uu___402_25778.wl_implicits)
          }  in
        (let uu____25780 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25780
         then
           let uu____25781 = FStar_Util.string_of_bool defer_ok  in
           let uu____25782 = wl_to_string wl  in
           let uu____25783 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____25781 uu____25782 uu____25783
         else ());
        (let g1 =
           let uu____25786 = solve_and_commit env wl fail1  in
           match uu____25786 with
           | FStar_Pervasives_Native.Some
               (uu____25793::uu____25794,uu____25795) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___403_25820 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___403_25820.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___403_25820.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____25821 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___404_25829 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___404_25829.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___404_25829.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___404_25829.FStar_TypeChecker_Env.implicits)
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
    let uu____25877 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25877 with
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
            let uu___405_25988 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___405_25988.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___405_25988.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___405_25988.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____25989 =
            let uu____25990 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____25990  in
          if uu____25989
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____25998 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____25999 =
                       let uu____26000 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____26000
                        in
                     FStar_Errors.diag uu____25998 uu____25999)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____26004 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____26005 =
                        let uu____26006 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____26006
                         in
                      FStar_Errors.diag uu____26004 uu____26005)
                   else ();
                   (let uu____26009 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____26009
                      "discharge_guard'" env vc1);
                   (let uu____26010 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____26010 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____26017 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26018 =
                                let uu____26019 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____26019
                                 in
                              FStar_Errors.diag uu____26017 uu____26018)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____26024 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26025 =
                                let uu____26026 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____26026
                                 in
                              FStar_Errors.diag uu____26024 uu____26025)
                           else ();
                           (let vcs =
                              let uu____26037 = FStar_Options.use_tactics ()
                                 in
                              if uu____26037
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____26057  ->
                                     (let uu____26059 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a236  -> ())
                                        uu____26059);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____26102  ->
                                              match uu____26102 with
                                              | (env1,goal,opts) ->
                                                  let uu____26118 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____26118, opts)))))
                              else
                                (let uu____26120 =
                                   let uu____26127 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____26127)  in
                                 [uu____26120])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____26160  ->
                                    match uu____26160 with
                                    | (env1,goal,opts) ->
                                        let uu____26170 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____26170 with
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
                                                (let uu____26178 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26179 =
                                                   let uu____26180 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____26181 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____26180 uu____26181
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26178 uu____26179)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____26184 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26185 =
                                                   let uu____26186 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____26186
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26184 uu____26185)
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
      let uu____26200 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26200 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26207 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26207
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26218 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26218 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____26235 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26235 with
      | FStar_Pervasives_Native.Some uu____26241 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26257 = try_teq false env t1 t2  in
        match uu____26257 with
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
            let uu____26287 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26287 with
            | FStar_Pervasives_Native.Some uu____26290 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26310 = acc  in
            match uu____26310 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26322 = hd1  in
                     (match uu____26322 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26327;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26335 = unresolved ctx_u  in
                             if uu____26335
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
                                       let uu___406_26351 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___406_26351.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           (uu___406_26351.FStar_TypeChecker_Env.imp_uvar);
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___406_26351.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___406_26351.FStar_TypeChecker_Env.imp_range);
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
                                    let uu___407_26359 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___407_26359.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___407_26359.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___407_26359.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___407_26359.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___407_26359.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___407_26359.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___407_26359.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___407_26359.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___407_26359.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___407_26359.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___407_26359.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___407_26359.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___407_26359.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___407_26359.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___407_26359.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___407_26359.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___407_26359.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___407_26359.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___407_26359.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___407_26359.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___407_26359.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___407_26359.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___407_26359.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___407_26359.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___407_26359.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___407_26359.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___407_26359.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___407_26359.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___407_26359.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___407_26359.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___407_26359.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___407_26359.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___407_26359.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___407_26359.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___407_26359.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___407_26359.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___407_26359.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___407_26359.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___407_26359.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___407_26359.FStar_TypeChecker_Env.dep_graph);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___407_26359.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___408_26362 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___408_26362.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___408_26362.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___408_26362.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___408_26362.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___408_26362.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___408_26362.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___408_26362.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___408_26362.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___408_26362.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___408_26362.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___408_26362.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___408_26362.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___408_26362.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___408_26362.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___408_26362.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___408_26362.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___408_26362.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___408_26362.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___408_26362.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___408_26362.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___408_26362.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___408_26362.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___408_26362.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___408_26362.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___408_26362.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___408_26362.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___408_26362.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___408_26362.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___408_26362.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___408_26362.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___408_26362.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___408_26362.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___408_26362.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___408_26362.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___408_26362.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___408_26362.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___408_26362.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___408_26362.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___408_26362.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___408_26362.FStar_TypeChecker_Env.dep_graph);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___408_26362.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26365 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26365
                                   then
                                     let uu____26366 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26367 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26368 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26369 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26366 uu____26367 uu____26368
                                       reason uu____26369
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26380 =
                                             let uu____26389 =
                                               let uu____26396 =
                                                 let uu____26397 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26398 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26399 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26397 uu____26398
                                                   uu____26399
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26396, r)
                                                in
                                             [uu____26389]  in
                                           FStar_Errors.add_errors
                                             uu____26380);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___411_26413 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___411_26413.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___411_26413.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___411_26413.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26416 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26426  ->
                                               let uu____26427 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26428 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26429 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26427 uu____26428
                                                 reason uu____26429)) env2 g2
                                         true
                                        in
                                     match uu____26416 with
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
          let uu___412_26431 = g  in
          let uu____26432 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___412_26431.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___412_26431.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___412_26431.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26432
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
        let uu____26466 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26466 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26467 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a237  -> ()) uu____26467
      | imp::uu____26469 ->
          let uu____26472 =
            let uu____26477 =
              let uu____26478 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26479 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26478 uu____26479 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26477)
             in
          FStar_Errors.raise_error uu____26472
            imp.FStar_TypeChecker_Env.imp_range
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___413_26490 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___413_26490.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___413_26490.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___413_26490.FStar_TypeChecker_Env.implicits)
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
        (let uu____26525 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26525
         then
           let uu____26526 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26527 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26526
             uu____26527
         else ());
        (let uu____26529 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26529 with
         | (prob,x,wl) ->
             let g =
               let uu____26548 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26558  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26548  in
             ((let uu____26578 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26578
               then
                 let uu____26579 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26580 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26581 =
                   let uu____26582 = FStar_Util.must g  in
                   guard_to_string env uu____26582  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26579 uu____26580 uu____26581
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
        let uu____26616 = check_subtyping env t1 t2  in
        match uu____26616 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26635 =
              let uu____26636 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____26636 g  in
            FStar_Pervasives_Native.Some uu____26635
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26654 = check_subtyping env t1 t2  in
        match uu____26654 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26673 =
              let uu____26674 =
                let uu____26675 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26675]  in
              FStar_TypeChecker_Env.close_guard env uu____26674 g  in
            FStar_Pervasives_Native.Some uu____26673
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26710 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26710
         then
           let uu____26711 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26712 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26711
             uu____26712
         else ());
        (let uu____26714 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26714 with
         | (prob,x,wl) ->
             let g =
               let uu____26727 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____26737  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26727  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26758 =
                      let uu____26759 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26759]  in
                    FStar_TypeChecker_Env.close_guard env uu____26758 g1  in
                  discharge_guard_nosmt env g2))
  