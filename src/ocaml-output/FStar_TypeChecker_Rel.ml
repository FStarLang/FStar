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
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Env.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__wl_implicits
  
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
                  let uu____388 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____388;
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
                   (let uu___371_423 = wl  in
                    {
                      attempting = (uu___371_423.attempting);
                      wl_deferred = (uu___371_423.wl_deferred);
                      ctr = (uu___371_423.ctr);
                      defer_ok = (uu___371_423.defer_ok);
                      smt_ok = (uu___371_423.smt_ok);
                      umax_heuristic_ok = (uu___371_423.umax_heuristic_ok);
                      tcenv = (uu___371_423.tcenv);
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
            let uu___372_455 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___372_455.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___372_455.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___372_455.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___372_455.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___372_455.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___372_455.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___372_455.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___372_455.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___372_455.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___372_455.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___372_455.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___372_455.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___372_455.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___372_455.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___372_455.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___372_455.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___372_455.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___372_455.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___372_455.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___372_455.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___372_455.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___372_455.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___372_455.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___372_455.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___372_455.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___372_455.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___372_455.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___372_455.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___372_455.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___372_455.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___372_455.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___372_455.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___372_455.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___372_455.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___372_455.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___372_455.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___372_455.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___372_455.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___372_455.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___372_455.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___372_455.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____457 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____457 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____494 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____524 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____549 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____555 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____561 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___339_576  ->
    match uu___339_576 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____582 = FStar_Syntax_Util.head_and_args t  in
    match uu____582 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____643 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____644 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____656 =
                     let uu____657 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____657  in
                   FStar_Util.format1 "@<%s>" uu____656
                in
             let uu____660 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____643 uu____644 uu____660
         | uu____661 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___340_671  ->
      match uu___340_671 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____675 =
            let uu____678 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____679 =
              let uu____682 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____683 =
                let uu____686 =
                  let uu____689 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____689]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____686
                 in
              uu____682 :: uu____683  in
            uu____678 :: uu____679  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____675
      | FStar_TypeChecker_Common.CProb p ->
          let uu____693 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____694 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____695 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____693 uu____694
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____695
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___341_705  ->
      match uu___341_705 with
      | UNIV (u,t) ->
          let x =
            let uu____709 = FStar_Options.hide_uvar_nums ()  in
            if uu____709
            then "?"
            else
              (let uu____711 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____711 FStar_Util.string_of_int)
             in
          let uu____712 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____712
      | TERM (u,t) ->
          let x =
            let uu____716 = FStar_Options.hide_uvar_nums ()  in
            if uu____716
            then "?"
            else
              (let uu____718 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____718 FStar_Util.string_of_int)
             in
          let uu____719 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____719
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____734 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____734 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____748 =
      let uu____751 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____751
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____748 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____764 .
    (FStar_Syntax_Syntax.term,'Auu____764) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____782 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____800  ->
              match uu____800 with
              | (x,uu____806) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____782 (FStar_String.concat " ")
  
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
        (let uu____836 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____836
         then
           let uu____837 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____837
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___342_843  ->
    match uu___342_843 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____848 .
    'Auu____848 FStar_TypeChecker_Common.problem ->
      'Auu____848 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___373_860 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___373_860.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___373_860.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___373_860.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___373_860.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___373_860.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___373_860.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___373_860.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____867 .
    'Auu____867 FStar_TypeChecker_Common.problem ->
      'Auu____867 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___343_884  ->
    match uu___343_884 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___344_899  ->
    match uu___344_899 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___374_905 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___374_905.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___374_905.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___374_905.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___374_905.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___374_905.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___374_905.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___374_905.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___374_905.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___374_905.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___375_913 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___375_913.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___375_913.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___375_913.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___375_913.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___375_913.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___375_913.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___375_913.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___375_913.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___375_913.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___345_925  ->
      match uu___345_925 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___346_930  ->
    match uu___346_930 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___347_941  ->
    match uu___347_941 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___348_954  ->
    match uu___348_954 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___349_967  ->
    match uu___349_967 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___350_980  ->
    match uu___350_980 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___351_993  ->
    match uu___351_993 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___352_1004  ->
    match uu___352_1004 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1019 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1019) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1047 =
          let uu____1048 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1048  in
        if uu____1047
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1082)::bs ->
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
          let uu____1128 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1152 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1152]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1128
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1180 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1204 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1204]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1180
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1247 =
          let uu____1248 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1248  in
        if uu____1247
        then ()
        else
          (let uu____1250 =
             let uu____1253 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1253
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1250 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1299 =
          let uu____1300 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1300  in
        if uu____1299
        then ()
        else
          (let uu____1302 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1302)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1319 =
        let uu____1320 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1320  in
      if uu____1319
      then ()
      else
        (let msgf m =
           let uu____1328 =
             let uu____1329 =
               let uu____1330 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1330 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1329  in
           Prims.strcat msg uu____1328  in
         (let uu____1332 = msgf "scope"  in
          let uu____1333 = p_scope prob  in
          def_scope_wf uu____1332 (p_loc prob) uu____1333);
         (let uu____1345 = msgf "guard"  in
          def_check_scoped uu____1345 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1350 = msgf "lhs"  in
                def_check_scoped uu____1350 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1351 = msgf "rhs"  in
                def_check_scoped uu____1351 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1356 = msgf "lhs"  in
                def_check_scoped_comp uu____1356 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1357 = msgf "rhs"  in
                def_check_scoped_comp uu____1357 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___376_1373 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___376_1373.wl_deferred);
          ctr = (uu___376_1373.ctr);
          defer_ok = (uu___376_1373.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___376_1373.umax_heuristic_ok);
          tcenv = (uu___376_1373.tcenv);
          wl_implicits = (uu___376_1373.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1380 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1380,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___377_1403 = empty_worklist env  in
      let uu____1404 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1404;
        wl_deferred = (uu___377_1403.wl_deferred);
        ctr = (uu___377_1403.ctr);
        defer_ok = (uu___377_1403.defer_ok);
        smt_ok = (uu___377_1403.smt_ok);
        umax_heuristic_ok = (uu___377_1403.umax_heuristic_ok);
        tcenv = (uu___377_1403.tcenv);
        wl_implicits = (uu___377_1403.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___378_1424 = wl  in
        {
          attempting = (uu___378_1424.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___378_1424.ctr);
          defer_ok = (uu___378_1424.defer_ok);
          smt_ok = (uu___378_1424.smt_ok);
          umax_heuristic_ok = (uu___378_1424.umax_heuristic_ok);
          tcenv = (uu___378_1424.tcenv);
          wl_implicits = (uu___378_1424.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___379_1446 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___379_1446.wl_deferred);
         ctr = (uu___379_1446.ctr);
         defer_ok = (uu___379_1446.defer_ok);
         smt_ok = (uu___379_1446.smt_ok);
         umax_heuristic_ok = (uu___379_1446.umax_heuristic_ok);
         tcenv = (uu___379_1446.tcenv);
         wl_implicits = (uu___379_1446.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1457 .
    worklist ->
      'Auu____1457 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1486 = FStar_Syntax_Util.type_u ()  in
          match uu____1486 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1498 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1498 with
               | (uu____1509,tt,wl1) ->
                   let uu____1512 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1512, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___353_1517  ->
    match uu___353_1517 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1533 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1533 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1543  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1637 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1637 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1637 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1637 FStar_TypeChecker_Common.problem,worklist)
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
                        let uu____1722 =
                          let uu____1731 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1731]  in
                        FStar_List.append scope uu____1722
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____1774 =
                      let uu____1777 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____1777  in
                    FStar_List.append uu____1774
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____1796 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1796 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____1815 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____1815;
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
                  (let uu____1883 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1883 with
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
                  (let uu____1966 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1966 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2002 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2002 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2002 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2002 FStar_TypeChecker_Common.problem,worklist)
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
                          let uu____2068 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2068]  in
                        let uu____2087 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2087
                     in
                  let uu____2090 =
                    let uu____2097 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___380_2107 = wl  in
                       {
                         attempting = (uu___380_2107.attempting);
                         wl_deferred = (uu___380_2107.wl_deferred);
                         ctr = (uu___380_2107.ctr);
                         defer_ok = (uu___380_2107.defer_ok);
                         smt_ok = (uu___380_2107.smt_ok);
                         umax_heuristic_ok =
                           (uu___380_2107.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___380_2107.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2097
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2090 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2119 =
                              let uu____2124 =
                                let uu____2125 =
                                  let uu____2134 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2134
                                   in
                                [uu____2125]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2124  in
                            uu____2119 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2164 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2164;
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
                let uu____2206 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2206;
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
  'Auu____2218 .
    worklist ->
      'Auu____2218 FStar_TypeChecker_Common.problem ->
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
              let uu____2251 =
                let uu____2254 =
                  let uu____2255 =
                    let uu____2262 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2262)  in
                  FStar_Syntax_Syntax.NT uu____2255  in
                [uu____2254]  in
              FStar_Syntax_Subst.subst uu____2251 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2282 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2282
        then
          let uu____2283 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2284 = prob_to_string env d  in
          let uu____2285 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2283 uu____2284 uu____2285 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2291 -> failwith "impossible"  in
           let uu____2292 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2304 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2305 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2304, uu____2305)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2309 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2310 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2309, uu____2310)
              in
           match uu____2292 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___354_2328  ->
            match uu___354_2328 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2340 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2344 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2344 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___355_2373  ->
           match uu___355_2373 with
           | UNIV uu____2376 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2383 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2383
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
        (fun uu___356_2407  ->
           match uu___356_2407 with
           | UNIV (u',t) ->
               let uu____2412 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2412
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2416 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2427 =
        let uu____2428 =
          let uu____2429 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2429
           in
        FStar_Syntax_Subst.compress uu____2428  in
      FStar_All.pipe_right uu____2427 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2440 =
        let uu____2441 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t
           in
        FStar_Syntax_Subst.compress uu____2441  in
      FStar_All.pipe_right uu____2440 FStar_Syntax_Util.unlazy_emb
  
let norm_arg :
  'Auu____2448 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2448) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2448)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2471 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2471, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2522  ->
              match uu____2522 with
              | (x,imp) ->
                  let uu____2541 =
                    let uu___381_2542 = x  in
                    let uu____2543 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___381_2542.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___381_2542.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2543
                    }  in
                  (uu____2541, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2566 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2566
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2570 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2570
        | uu____2573 -> u2  in
      let uu____2574 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2574
  
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
                (let uu____2686 = norm_refinement env t12  in
                 match uu____2686 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2701;
                     FStar_Syntax_Syntax.vars = uu____2702;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2726 =
                       let uu____2727 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2728 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2727 uu____2728
                        in
                     failwith uu____2726)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2742 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2742
          | FStar_Syntax_Syntax.Tm_uinst uu____2743 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2778 =
                   let uu____2779 = FStar_Syntax_Subst.compress t1'  in
                   uu____2779.FStar_Syntax_Syntax.n  in
                 match uu____2778 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2794 -> aux true t1'
                 | uu____2801 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2816 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2845 =
                   let uu____2846 = FStar_Syntax_Subst.compress t1'  in
                   uu____2846.FStar_Syntax_Syntax.n  in
                 match uu____2845 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2861 -> aux true t1'
                 | uu____2868 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2883 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2928 =
                   let uu____2929 = FStar_Syntax_Subst.compress t1'  in
                   uu____2929.FStar_Syntax_Syntax.n  in
                 match uu____2928 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2944 -> aux true t1'
                 | uu____2951 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2966 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2981 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2996 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3011 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3026 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3055 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3088 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3109 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3136 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3163 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3200 ->
              let uu____3207 =
                let uu____3208 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3209 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3208 uu____3209
                 in
              failwith uu____3207
          | FStar_Syntax_Syntax.Tm_ascribed uu____3222 ->
              let uu____3249 =
                let uu____3250 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3251 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3250 uu____3251
                 in
              failwith uu____3249
          | FStar_Syntax_Syntax.Tm_delayed uu____3264 ->
              let uu____3287 =
                let uu____3288 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3289 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3288 uu____3289
                 in
              failwith uu____3287
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3302 =
                let uu____3303 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3304 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3303 uu____3304
                 in
              failwith uu____3302
           in
        let uu____3317 = whnf env t1  in aux false uu____3317
  
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
      let uu____3373 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3373 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3413 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3413, FStar_Syntax_Util.t_true)
  
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
        let uu____3437 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3437 with
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
  fun uu____3496  ->
    match uu____3496 with
    | (t_base,refopt) ->
        let uu____3527 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3527 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3565 =
      let uu____3568 =
        let uu____3571 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3594  ->
                  match uu____3594 with | (uu____3601,uu____3602,x) -> x))
           in
        FStar_List.append wl.attempting uu____3571  in
      FStar_List.map (wl_prob_to_string wl) uu____3568  in
    FStar_All.pipe_right uu____3565 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____3616 .
    ('Auu____3616,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3627  ->
    match uu____3627 with
    | (uu____3634,c,args) ->
        let uu____3637 = print_ctx_uvar c  in
        let uu____3638 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3637 uu____3638
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3644 = FStar_Syntax_Util.head_and_args t  in
    match uu____3644 with
    | (head1,_args) ->
        let uu____3687 =
          let uu____3688 = FStar_Syntax_Subst.compress head1  in
          uu____3688.FStar_Syntax_Syntax.n  in
        (match uu____3687 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3691 -> true
         | uu____3704 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3710 = FStar_Syntax_Util.head_and_args t  in
    match uu____3710 with
    | (head1,_args) ->
        let uu____3753 =
          let uu____3754 = FStar_Syntax_Subst.compress head1  in
          uu____3754.FStar_Syntax_Syntax.n  in
        (match uu____3753 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____3758) -> u
         | uu____3775 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____3798 = FStar_Syntax_Util.head_and_args t  in
      match uu____3798 with
      | (head1,args) ->
          let uu____3845 =
            let uu____3846 = FStar_Syntax_Subst.compress head1  in
            uu____3846.FStar_Syntax_Syntax.n  in
          (match uu____3845 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____3854)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____3887 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___357_3912  ->
                         match uu___357_3912 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____3916 =
                               let uu____3917 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____3917.FStar_Syntax_Syntax.n  in
                             (match uu____3916 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____3921 -> false)
                         | uu____3922 -> true))
                  in
               (match uu____3887 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____3946 =
                        FStar_List.collect
                          (fun uu___358_3958  ->
                             match uu___358_3958 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____3962 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____3962]
                             | uu____3963 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____3946 FStar_List.rev  in
                    let uu____3986 =
                      let uu____3993 =
                        let uu____4002 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___359_4024  ->
                                  match uu___359_4024 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4028 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4028]
                                  | uu____4029 -> []))
                           in
                        FStar_All.pipe_right uu____4002 FStar_List.rev  in
                      let uu____4052 =
                        let uu____4055 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4055  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____3993 uu____4052
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____3986 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4090  ->
                                match uu____4090 with
                                | (x,i) ->
                                    let uu____4109 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4109, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4140  ->
                                match uu____4140 with
                                | (a,i) ->
                                    let uu____4159 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4159, i)) args_sol
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
           | uu____4181 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4201 =
          let uu____4224 =
            let uu____4225 = FStar_Syntax_Subst.compress k  in
            uu____4225.FStar_Syntax_Syntax.n  in
          match uu____4224 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4306 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4306)
              else
                (let uu____4340 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4340 with
                 | (ys',t1,uu____4373) ->
                     let uu____4378 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4378))
          | uu____4417 ->
              let uu____4418 =
                let uu____4423 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4423)  in
              ((ys, t), uu____4418)
           in
        match uu____4201 with
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
                 let uu____4516 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4516 c  in
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
               (let uu____4590 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4590
                then
                  let uu____4591 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4592 = print_ctx_uvar uv  in
                  let uu____4593 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4591 uu____4592 uu____4593
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4599 =
                   let uu____4600 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4600  in
                 let uu____4601 =
                   let uu____4604 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4604
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____4599 uu____4601 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____4637 =
               let uu____4638 =
                 let uu____4639 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____4640 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____4639 uu____4640
                  in
               failwith uu____4638  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____4704  ->
                       match uu____4704 with
                       | (a,i) ->
                           let uu____4725 =
                             let uu____4726 = FStar_Syntax_Subst.compress a
                                in
                             uu____4726.FStar_Syntax_Syntax.n  in
                           (match uu____4725 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____4752 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____4762 =
                 let uu____4763 = is_flex g  in Prims.op_Negation uu____4763
                  in
               if uu____4762
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____4767 = destruct_flex_t g wl  in
                  match uu____4767 with
                  | ((uu____4772,uv1,args),wl1) ->
                      ((let uu____4777 = args_as_binders args  in
                        assign_solution uu____4777 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___382_4779 = wl1  in
              {
                attempting = (uu___382_4779.attempting);
                wl_deferred = (uu___382_4779.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___382_4779.defer_ok);
                smt_ok = (uu___382_4779.smt_ok);
                umax_heuristic_ok = (uu___382_4779.umax_heuristic_ok);
                tcenv = (uu___382_4779.tcenv);
                wl_implicits = (uu___382_4779.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4800 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4800
         then
           let uu____4801 = FStar_Util.string_of_int pid  in
           let uu____4802 =
             let uu____4803 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4803 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4801 uu____4802
         else ());
        commit sol;
        (let uu___383_4810 = wl  in
         {
           attempting = (uu___383_4810.attempting);
           wl_deferred = (uu___383_4810.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___383_4810.defer_ok);
           smt_ok = (uu___383_4810.smt_ok);
           umax_heuristic_ok = (uu___383_4810.umax_heuristic_ok);
           tcenv = (uu___383_4810.tcenv);
           wl_implicits = (uu___383_4810.wl_implicits)
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
             | (uu____4872,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4900 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4900
              in
           (let uu____4906 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4906
            then
              let uu____4907 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4908 =
                let uu____4909 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4909 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4907 uu____4908
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
        let uu____4934 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4934 FStar_Util.set_elements  in
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
      let uu____4968 = occurs uk t  in
      match uu____4968 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4997 =
                 let uu____4998 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4999 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4998 uu____4999
                  in
               FStar_Pervasives_Native.Some uu____4997)
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
            let uu____5112 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5112 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5162 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5218  ->
             match uu____5218 with
             | (x,uu____5230) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5247 = FStar_List.last bs  in
      match uu____5247 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5271) ->
          let uu____5282 =
            FStar_Util.prefix_until
              (fun uu___360_5297  ->
                 match uu___360_5297 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5299 -> false) g
             in
          (match uu____5282 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5312,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5348 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5348 with
        | (pfx,uu____5358) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5370 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5370 with
             | (uu____5377,src',wl1) ->
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
                 | uu____5489 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5490 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5554  ->
                  fun uu____5555  ->
                    match (uu____5554, uu____5555) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5658 =
                          let uu____5659 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5659
                           in
                        if uu____5658
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5688 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5688
                           then
                             let uu____5703 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5703)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5490 with | (isect,uu____5752) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5787 'Auu____5788 .
    (FStar_Syntax_Syntax.bv,'Auu____5787) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5788) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5845  ->
              fun uu____5846  ->
                match (uu____5845, uu____5846) with
                | ((a,uu____5864),(b,uu____5866)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5881 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5881) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5911  ->
           match uu____5911 with
           | (y,uu____5917) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5926 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5926) FStar_Pervasives_Native.tuple2
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
                   let uu____6088 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6088
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6118 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6165 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6203 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6216 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___361_6221  ->
    match uu___361_6221 with
    | MisMatch (d1,d2) ->
        let uu____6232 =
          let uu____6233 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6234 =
            let uu____6235 =
              let uu____6236 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6236 ")"  in
            Prims.strcat ") (" uu____6235  in
          Prims.strcat uu____6233 uu____6234  in
        Prims.strcat "MisMatch (" uu____6232
    | HeadMatch u ->
        let uu____6238 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6238
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___362_6243  ->
    match uu___362_6243 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6258 -> HeadMatch false
  
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
          let uu____6273 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6273 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6284 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6307 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6316 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6342 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6342
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6343 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6344 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6345 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6358 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6371 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6395) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6401,uu____6402) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6444) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6469;
             FStar_Syntax_Syntax.index = uu____6470;
             FStar_Syntax_Syntax.sort = t2;_},uu____6472)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6479 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6480 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6481 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6496 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6503 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6523 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6523
  
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
           { FStar_Syntax_Syntax.blob = uu____6541;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6542;
             FStar_Syntax_Syntax.ltyp = uu____6543;
             FStar_Syntax_Syntax.rng = uu____6544;_},uu____6545)
            ->
            let uu____6556 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____6556 t21
        | (uu____6557,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____6558;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6559;
             FStar_Syntax_Syntax.ltyp = uu____6560;
             FStar_Syntax_Syntax.rng = uu____6561;_})
            ->
            let uu____6572 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____6572
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____6582 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6582
            then FullMatch
            else
              (let uu____6584 =
                 let uu____6593 =
                   let uu____6596 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6596  in
                 let uu____6597 =
                   let uu____6600 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6600  in
                 (uu____6593, uu____6597)  in
               MisMatch uu____6584)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6606),FStar_Syntax_Syntax.Tm_uinst (g,uu____6608)) ->
            let uu____6617 = head_matches env f g  in
            FStar_All.pipe_right uu____6617 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6620 = FStar_Const.eq_const c d  in
            if uu____6620
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6627),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6629)) ->
            let uu____6662 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6662
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6669),FStar_Syntax_Syntax.Tm_refine (y,uu____6671)) ->
            let uu____6680 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6680 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6682),uu____6683) ->
            let uu____6688 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6688 head_match
        | (uu____6689,FStar_Syntax_Syntax.Tm_refine (x,uu____6691)) ->
            let uu____6696 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6696 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6697,FStar_Syntax_Syntax.Tm_type
           uu____6698) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6699,FStar_Syntax_Syntax.Tm_arrow uu____6700) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6730),FStar_Syntax_Syntax.Tm_app (head',uu____6732))
            ->
            let uu____6781 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6781 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6783),uu____6784) ->
            let uu____6809 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6809 head_match
        | (uu____6810,FStar_Syntax_Syntax.Tm_app (head1,uu____6812)) ->
            let uu____6837 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6837 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6838,FStar_Syntax_Syntax.Tm_let
           uu____6839) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6864,FStar_Syntax_Syntax.Tm_match uu____6865) ->
            HeadMatch true
        | uu____6910 ->
            let uu____6915 =
              let uu____6924 = delta_depth_of_term env t11  in
              let uu____6927 = delta_depth_of_term env t21  in
              (uu____6924, uu____6927)  in
            MisMatch uu____6915
  
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
          (let uu____6987 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6987
           then
             let uu____6988 = FStar_Syntax_Print.term_to_string t  in
             let uu____6989 = FStar_Syntax_Print.term_to_string head1  in
             FStar_Util.print2 "Head of %s is %s\n" uu____6988 uu____6989
           else ());
          (let uu____6991 =
             let uu____6992 = FStar_Syntax_Util.un_uinst head1  in
             uu____6992.FStar_Syntax_Syntax.n  in
           match uu____6991 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____6998 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant;
                   FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____6998 with
                | FStar_Pervasives_Native.None  ->
                    ((let uu____7012 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7012
                      then
                        let uu____7013 =
                          FStar_Syntax_Print.term_to_string head1  in
                        FStar_Util.print1 "No definition found for %s\n"
                          uu____7013
                      else ());
                     FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.Some uu____7015 ->
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
                    ((let uu____7026 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "RelDelta")
                         in
                      if uu____7026
                      then
                        let uu____7027 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____7028 = FStar_Syntax_Print.term_to_string t'
                           in
                        FStar_Util.print2 "Inlined %s to %s\n" uu____7027
                          uu____7028
                      else ());
                     FStar_Pervasives_Native.Some t'))
           | uu____7030 -> FStar_Pervasives_Native.None)
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
          (let uu____7168 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7168
           then
             let uu____7169 = FStar_Syntax_Print.term_to_string t11  in
             let uu____7170 = FStar_Syntax_Print.term_to_string t21  in
             let uu____7171 = string_of_match_result r  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7169
               uu____7170 uu____7171
           else ());
          (let reduce_one_and_try_again d1 d2 =
             let d1_greater_than_d2 =
               FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
             let uu____7195 =
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
             match uu____7195 with
             | (t12,t22) ->
                 aux retry (n_delta + (Prims.parse_int "1")) t12 t22
              in
           let reduce_both_and_try_again d r1 =
             let uu____7240 = FStar_TypeChecker_Common.decr_delta_depth d  in
             match uu____7240 with
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
                uu____7272),uu____7273)
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7291 =
                    let uu____7300 = maybe_inline t11  in
                    let uu____7303 = maybe_inline t21  in
                    (uu____7300, uu____7303)  in
                  match uu____7291 with
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
               (uu____7340,FStar_Pervasives_Native.Some
                (FStar_Syntax_Syntax.Delta_equational_at_level uu____7341))
               ->
               if Prims.op_Negation retry
               then fail1 n_delta r t11 t21
               else
                 (let uu____7359 =
                    let uu____7368 = maybe_inline t11  in
                    let uu____7371 = maybe_inline t21  in
                    (uu____7368, uu____7371)  in
                  match uu____7359 with
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
           | MisMatch uu____7420 -> fail1 n_delta r t11 t21
           | uu____7429 -> success n_delta r t11 t21)
           in
        let r = aux true (Prims.parse_int "0") t1 t2  in
        (let uu____7442 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelDelta")
            in
         if uu____7442
         then
           let uu____7443 = FStar_Syntax_Print.term_to_string t1  in
           let uu____7444 = FStar_Syntax_Print.term_to_string t2  in
           let uu____7445 =
             string_of_match_result (FStar_Pervasives_Native.fst r)  in
           let uu____7452 =
             if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
             then "None"
             else
               (let uu____7464 =
                  FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____7464
                  (fun uu____7498  ->
                     match uu____7498 with
                     | (t11,t21) ->
                         let uu____7505 =
                           FStar_Syntax_Print.term_to_string t11  in
                         let uu____7506 =
                           let uu____7507 =
                             FStar_Syntax_Print.term_to_string t21  in
                           Prims.strcat "; " uu____7507  in
                         Prims.strcat uu____7505 uu____7506))
              in
           FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
             uu____7443 uu____7444 uu____7445 uu____7452
         else ());
        r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7519 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7519 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___363_7532  ->
    match uu___363_7532 with
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
      let uu___384_7569 = p  in
      let uu____7572 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7573 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___384_7569.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7572;
        FStar_TypeChecker_Common.relation =
          (uu___384_7569.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7573;
        FStar_TypeChecker_Common.element =
          (uu___384_7569.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___384_7569.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___384_7569.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___384_7569.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___384_7569.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___384_7569.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7587 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7587
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7592 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7614 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7614 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7622 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7622 with
           | (lh,lhs_args) ->
               let uu____7669 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7669 with
                | (rh,rhs_args) ->
                    let uu____7716 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7729,FStar_Syntax_Syntax.Tm_uvar uu____7730)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7819 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7846,uu____7847)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7862,FStar_Syntax_Syntax.Tm_uvar uu____7863)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7878,FStar_Syntax_Syntax.Tm_arrow uu____7879)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___385_7909 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___385_7909.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___385_7909.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___385_7909.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___385_7909.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___385_7909.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___385_7909.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___385_7909.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___385_7909.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___385_7909.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7912,FStar_Syntax_Syntax.Tm_type uu____7913)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___385_7929 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___385_7929.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___385_7929.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___385_7929.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___385_7929.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___385_7929.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___385_7929.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___385_7929.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___385_7929.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___385_7929.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7932,FStar_Syntax_Syntax.Tm_uvar uu____7933)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___385_7949 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___385_7949.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___385_7949.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___385_7949.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___385_7949.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___385_7949.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___385_7949.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___385_7949.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___385_7949.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___385_7949.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7952,FStar_Syntax_Syntax.Tm_uvar uu____7953)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7968,uu____7969)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7984,FStar_Syntax_Syntax.Tm_uvar uu____7985)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8000,uu____8001) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7716 with
                     | (rank,tp1) ->
                         let uu____8014 =
                           FStar_All.pipe_right
                             (let uu___386_8018 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___386_8018.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___386_8018.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___386_8018.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___386_8018.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___386_8018.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___386_8018.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___386_8018.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___386_8018.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___386_8018.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____8014))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8024 =
            FStar_All.pipe_right
              (let uu___387_8028 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___387_8028.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___387_8028.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___387_8028.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___387_8028.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___387_8028.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___387_8028.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___387_8028.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___387_8028.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___387_8028.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8024)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8089 probs =
      match uu____8089 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8170 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8191 = rank wl.tcenv hd1  in
               (match uu____8191 with
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
                      (let uu____8250 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8254 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8254)
                          in
                       if uu____8250
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
          let uu____8322 = FStar_Syntax_Util.head_and_args t  in
          match uu____8322 with
          | (hd1,uu____8340) ->
              let uu____8365 =
                let uu____8366 = FStar_Syntax_Subst.compress hd1  in
                uu____8366.FStar_Syntax_Syntax.n  in
              (match uu____8365 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8370) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8404  ->
                           match uu____8404 with
                           | (y,uu____8412) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8434  ->
                                       match uu____8434 with
                                       | (x,uu____8442) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8447 -> false)
           in
        let uu____8448 = rank tcenv p  in
        match uu____8448 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8455 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8482 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8496 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8510 -> false
  
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
                        let uu____8562 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8562 with
                        | (k,uu____8568) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8578 -> false)))
            | uu____8579 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8631 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8637 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8637 = (Prims.parse_int "0")))
                           in
                        if uu____8631 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8653 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8659 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8659 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8653)
               in
            let uu____8660 = filter1 u12  in
            let uu____8663 = filter1 u22  in (uu____8660, uu____8663)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____8693 = filter_out_common_univs us1 us2  in
                   (match uu____8693 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____8752 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____8752 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____8755 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____8765 =
                             let uu____8766 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____8767 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____8766 uu____8767
                              in
                           UFailed uu____8765))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____8791 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____8791 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____8817 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____8817 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____8820 ->
                   let uu____8825 =
                     let uu____8826 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____8827 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____8826
                       uu____8827 msg
                      in
                   UFailed uu____8825)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8828,uu____8829) ->
              let uu____8830 =
                let uu____8831 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8832 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8831 uu____8832
                 in
              failwith uu____8830
          | (FStar_Syntax_Syntax.U_unknown ,uu____8833) ->
              let uu____8834 =
                let uu____8835 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8836 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8835 uu____8836
                 in
              failwith uu____8834
          | (uu____8837,FStar_Syntax_Syntax.U_bvar uu____8838) ->
              let uu____8839 =
                let uu____8840 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8841 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8840 uu____8841
                 in
              failwith uu____8839
          | (uu____8842,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8843 =
                let uu____8844 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8845 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8844 uu____8845
                 in
              failwith uu____8843
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8869 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8869
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8883 = occurs_univ v1 u3  in
              if uu____8883
              then
                let uu____8884 =
                  let uu____8885 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8886 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8885 uu____8886
                   in
                try_umax_components u11 u21 uu____8884
              else
                (let uu____8888 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8888)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8900 = occurs_univ v1 u3  in
              if uu____8900
              then
                let uu____8901 =
                  let uu____8902 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8903 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8902 uu____8903
                   in
                try_umax_components u11 u21 uu____8901
              else
                (let uu____8905 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8905)
          | (FStar_Syntax_Syntax.U_max uu____8906,uu____8907) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8913 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8913
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8915,FStar_Syntax_Syntax.U_max uu____8916) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8922 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8922
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8924,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8925,FStar_Syntax_Syntax.U_name
             uu____8926) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8927) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8928) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8929,FStar_Syntax_Syntax.U_succ
             uu____8930) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8931,FStar_Syntax_Syntax.U_zero
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
      let uu____9031 = bc1  in
      match uu____9031 with
      | (bs1,mk_cod1) ->
          let uu____9075 = bc2  in
          (match uu____9075 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9186 = aux xs ys  in
                     (match uu____9186 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9269 =
                       let uu____9276 = mk_cod1 xs  in ([], uu____9276)  in
                     let uu____9279 =
                       let uu____9286 = mk_cod2 ys  in ([], uu____9286)  in
                     (uu____9269, uu____9279)
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
                  let uu____9354 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9354 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9357 =
                    let uu____9358 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9358 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9357
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9363 = has_type_guard t1 t2  in (uu____9363, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9364 = has_type_guard t2 t1  in (uu____9364, wl)
  
let is_flex_pat :
  'Auu____9373 'Auu____9374 'Auu____9375 .
    ('Auu____9373,'Auu____9374,'Auu____9375 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___364_9388  ->
    match uu___364_9388 with
    | (uu____9397,uu____9398,[]) -> true
    | uu____9401 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9432 = f  in
      match uu____9432 with
      | (uu____9439,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9440;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9441;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9444;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9445;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9446;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9506  ->
                 match uu____9506 with
                 | (y,uu____9514) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9668 =
                  let uu____9683 =
                    let uu____9686 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9686  in
                  ((FStar_List.rev pat_binders), uu____9683)  in
                FStar_Pervasives_Native.Some uu____9668
            | (uu____9719,[]) ->
                let uu____9750 =
                  let uu____9765 =
                    let uu____9768 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9768  in
                  ((FStar_List.rev pat_binders), uu____9765)  in
                FStar_Pervasives_Native.Some uu____9750
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9859 =
                  let uu____9860 = FStar_Syntax_Subst.compress a  in
                  uu____9860.FStar_Syntax_Syntax.n  in
                (match uu____9859 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9880 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9880
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___388_9907 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___388_9907.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___388_9907.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9911 =
                            let uu____9912 =
                              let uu____9919 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9919)  in
                            FStar_Syntax_Syntax.NT uu____9912  in
                          [uu____9911]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___389_9935 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___389_9935.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___389_9935.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9936 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9976 =
                  let uu____9991 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9991  in
                (match uu____9976 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10066 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10099 ->
               let uu____10100 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10100 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10419 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10419
       then
         let uu____10420 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10420
       else ());
      (let uu____10422 = next_prob probs  in
       match uu____10422 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___390_10449 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___390_10449.wl_deferred);
               ctr = (uu___390_10449.ctr);
               defer_ok = (uu___390_10449.defer_ok);
               smt_ok = (uu___390_10449.smt_ok);
               umax_heuristic_ok = (uu___390_10449.umax_heuristic_ok);
               tcenv = (uu___390_10449.tcenv);
               wl_implicits = (uu___390_10449.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10457 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10457
                 then
                   let uu____10458 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10458
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
                           (let uu___391_10463 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___391_10463.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___391_10463.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___391_10463.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___391_10463.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___391_10463.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___391_10463.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___391_10463.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___391_10463.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___391_10463.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10485 ->
                let uu____10494 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10553  ->
                          match uu____10553 with
                          | (c,uu____10561,uu____10562) -> c < probs.ctr))
                   in
                (match uu____10494 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10603 =
                            let uu____10608 =
                              FStar_List.map
                                (fun uu____10623  ->
                                   match uu____10623 with
                                   | (uu____10634,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10608, (probs.wl_implicits))  in
                          Success uu____10603
                      | uu____10637 ->
                          let uu____10646 =
                            let uu___392_10647 = probs  in
                            let uu____10648 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10667  ->
                                      match uu____10667 with
                                      | (uu____10674,uu____10675,y) -> y))
                               in
                            {
                              attempting = uu____10648;
                              wl_deferred = rest;
                              ctr = (uu___392_10647.ctr);
                              defer_ok = (uu___392_10647.defer_ok);
                              smt_ok = (uu___392_10647.smt_ok);
                              umax_heuristic_ok =
                                (uu___392_10647.umax_heuristic_ok);
                              tcenv = (uu___392_10647.tcenv);
                              wl_implicits = (uu___392_10647.wl_implicits)
                            }  in
                          solve env uu____10646))))

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
            let uu____10682 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10682 with
            | USolved wl1 ->
                let uu____10684 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10684
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
                  let uu____10736 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10736 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10739 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10751;
                  FStar_Syntax_Syntax.vars = uu____10752;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10755;
                  FStar_Syntax_Syntax.vars = uu____10756;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10768,uu____10769) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10776,FStar_Syntax_Syntax.Tm_uinst uu____10777) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10784 -> USolved wl

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
            ((let uu____10794 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10794
              then
                let uu____10795 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10795 msg
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
               let uu____10881 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10881 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10934 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10934
                then
                  let uu____10935 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10936 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10935 uu____10936
                else ());
               (let uu____10938 = head_matches_delta env1 t1 t2  in
                match uu____10938 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10983 = eq_prob t1 t2 wl2  in
                         (match uu____10983 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11004 ->
                         let uu____11013 = eq_prob t1 t2 wl2  in
                         (match uu____11013 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11062 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11077 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11078 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11077, uu____11078)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11083 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11084 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11083, uu____11084)
                            in
                         (match uu____11062 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11115 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11115 with
                                | (t1_hd,t1_args) ->
                                    let uu____11160 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11160 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11224 =
                                              let uu____11231 =
                                                let uu____11242 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11242 :: t1_args  in
                                              let uu____11259 =
                                                let uu____11268 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11268 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11317  ->
                                                   fun uu____11318  ->
                                                     fun uu____11319  ->
                                                       match (uu____11317,
                                                               uu____11318,
                                                               uu____11319)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11369),
                                                          (a2,uu____11371))
                                                           ->
                                                           let uu____11408 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11408
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11231
                                                uu____11259
                                               in
                                            match uu____11224 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___393_11434 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___393_11434.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___393_11434.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___393_11434.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11442 =
                                                  solve env1 wl'  in
                                                (match uu____11442 with
                                                 | Success (uu____11445,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___394_11449
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___394_11449.attempting);
                                                            wl_deferred =
                                                              (uu___394_11449.wl_deferred);
                                                            ctr =
                                                              (uu___394_11449.ctr);
                                                            defer_ok =
                                                              (uu___394_11449.defer_ok);
                                                            smt_ok =
                                                              (uu___394_11449.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___394_11449.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___394_11449.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11450 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11482 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11482 with
                                | (t1_base,p1_opt) ->
                                    let uu____11517 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11517 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11615 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11615
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
                                               let uu____11663 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11663
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
                                               let uu____11693 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11693
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
                                               let uu____11723 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11723
                                           | uu____11726 -> t_base  in
                                         let uu____11743 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11743 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11757 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11757, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11764 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11764 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11799 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11799 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11834 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11834
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
                              let uu____11858 = combine t11 t21 wl2  in
                              (match uu____11858 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11891 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11891
                                     then
                                       let uu____11892 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11892
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11931 ts1 =
               match uu____11931 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____11994 = pairwise out t wl2  in
                        (match uu____11994 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12030 =
               let uu____12041 = FStar_List.hd ts  in (uu____12041, [], wl1)
                in
             let uu____12050 = FStar_List.tl ts  in
             aux uu____12030 uu____12050  in
           let uu____12057 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12057 with
           | (this_flex,this_rigid) ->
               let uu____12081 =
                 let uu____12082 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12082.FStar_Syntax_Syntax.n  in
               (match uu____12081 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12107 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12107
                    then
                      let uu____12108 = destruct_flex_t this_flex wl  in
                      (match uu____12108 with
                       | (flex,wl1) ->
                           let uu____12115 = quasi_pattern env flex  in
                           (match uu____12115 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12133 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12133
                                  then
                                    let uu____12134 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12134
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12137 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___395_12140 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___395_12140.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___395_12140.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___395_12140.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___395_12140.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___395_12140.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___395_12140.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___395_12140.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___395_12140.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___395_12140.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12137)
                | uu____12141 ->
                    ((let uu____12143 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12143
                      then
                        let uu____12144 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12144
                      else ());
                     (let uu____12146 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12146 with
                      | (u,_args) ->
                          let uu____12189 =
                            let uu____12190 = FStar_Syntax_Subst.compress u
                               in
                            uu____12190.FStar_Syntax_Syntax.n  in
                          (match uu____12189 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12217 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12217 with
                                 | (u',uu____12235) ->
                                     let uu____12260 =
                                       let uu____12261 = whnf env u'  in
                                       uu____12261.FStar_Syntax_Syntax.n  in
                                     (match uu____12260 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12282 -> false)
                                  in
                               let uu____12283 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___365_12306  ->
                                         match uu___365_12306 with
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
                                              | uu____12315 -> false)
                                         | uu____12318 -> false))
                                  in
                               (match uu____12283 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12332 = whnf env this_rigid
                                         in
                                      let uu____12333 =
                                        FStar_List.collect
                                          (fun uu___366_12339  ->
                                             match uu___366_12339 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12345 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12345]
                                             | uu____12347 -> [])
                                          bounds_probs
                                         in
                                      uu____12332 :: uu____12333  in
                                    let uu____12348 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12348 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12379 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12394 =
                                               let uu____12395 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12395.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12394 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12407 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12407)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12416 -> bound  in
                                           let uu____12417 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12417)  in
                                         (match uu____12379 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12446 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12446
                                                then
                                                  let wl'1 =
                                                    let uu___396_12448 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___396_12448.wl_deferred);
                                                      ctr =
                                                        (uu___396_12448.ctr);
                                                      defer_ok =
                                                        (uu___396_12448.defer_ok);
                                                      smt_ok =
                                                        (uu___396_12448.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___396_12448.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___396_12448.tcenv);
                                                      wl_implicits =
                                                        (uu___396_12448.wl_implicits)
                                                    }  in
                                                  let uu____12449 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12449
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12452 =
                                                  solve_t env eq_prob
                                                    (let uu___397_12454 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___397_12454.wl_deferred);
                                                       ctr =
                                                         (uu___397_12454.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___397_12454.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___397_12454.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___397_12454.tcenv);
                                                       wl_implicits =
                                                         (uu___397_12454.wl_implicits)
                                                     })
                                                   in
                                                match uu____12452 with
                                                | Success uu____12455 ->
                                                    let wl2 =
                                                      let uu___398_12461 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___398_12461.wl_deferred);
                                                        ctr =
                                                          (uu___398_12461.ctr);
                                                        defer_ok =
                                                          (uu___398_12461.defer_ok);
                                                        smt_ok =
                                                          (uu___398_12461.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___398_12461.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___398_12461.tcenv);
                                                        wl_implicits =
                                                          (uu___398_12461.wl_implicits)
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
                                                    let uu____12476 =
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
                                                    ((let uu____12487 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12487
                                                      then
                                                        let uu____12488 =
                                                          let uu____12489 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12489
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12488
                                                      else ());
                                                     (let uu____12495 =
                                                        let uu____12510 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12510)
                                                         in
                                                      match uu____12495 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12532))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12558 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12558
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
                                                                  let uu____12575
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12575))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12600 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12600
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
                                                                    let uu____12618
                                                                    =
                                                                    let uu____12623
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12623
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12618
                                                                    [] wl2
                                                                     in
                                                                  let uu____12628
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12628))))
                                                      | uu____12629 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12644 when flip ->
                               let uu____12645 =
                                 let uu____12646 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12647 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12646 uu____12647
                                  in
                               failwith uu____12645
                           | uu____12648 ->
                               let uu____12649 =
                                 let uu____12650 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12651 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12650 uu____12651
                                  in
                               failwith uu____12649)))))

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
                      (fun uu____12685  ->
                         match uu____12685 with
                         | (x,i) ->
                             let uu____12704 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12704, i)) bs_lhs
                     in
                  let uu____12707 = lhs  in
                  match uu____12707 with
                  | (uu____12708,u_lhs,uu____12710) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12807 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12817 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12817, univ)
                             in
                          match uu____12807 with
                          | (k,univ) ->
                              let uu____12824 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12824 with
                               | (uu____12841,u,wl3) ->
                                   let uu____12844 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12844, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12870 =
                              let uu____12883 =
                                let uu____12894 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12894 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12945  ->
                                   fun uu____12946  ->
                                     match (uu____12945, uu____12946) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13047 =
                                           let uu____13054 =
                                             let uu____13057 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13057
                                              in
                                           copy_uvar u_lhs [] uu____13054 wl2
                                            in
                                         (match uu____13047 with
                                          | (uu____13086,t_a,wl3) ->
                                              let uu____13089 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13089 with
                                               | (uu____13108,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12883
                                ([], wl1)
                               in
                            (match uu____12870 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___399_13164 = ct  in
                                   let uu____13165 =
                                     let uu____13168 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13168
                                      in
                                   let uu____13183 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___399_13164.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___399_13164.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13165;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13183;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___399_13164.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___400_13201 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___400_13201.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___400_13201.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13204 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13204 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13266 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13266 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13277 =
                                          let uu____13282 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13282)  in
                                        TERM uu____13277  in
                                      let uu____13283 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13283 with
                                       | (sub_prob,wl3) ->
                                           let uu____13296 =
                                             let uu____13297 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13297
                                              in
                                           solve env uu____13296))
                             | (x,imp)::formals2 ->
                                 let uu____13319 =
                                   let uu____13326 =
                                     let uu____13329 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13329
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13326 wl1
                                    in
                                 (match uu____13319 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13350 =
                                          let uu____13353 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13353
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13350 u_x
                                         in
                                      let uu____13354 =
                                        let uu____13357 =
                                          let uu____13360 =
                                            let uu____13361 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13361, imp)  in
                                          [uu____13360]  in
                                        FStar_List.append bs_terms
                                          uu____13357
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13354 formals2 wl2)
                              in
                           let uu____13388 = occurs_check u_lhs arrow1  in
                           (match uu____13388 with
                            | (uu____13399,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13410 =
                                    let uu____13411 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13411
                                     in
                                  giveup_or_defer env orig wl uu____13410
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
              (let uu____13440 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13440
               then
                 let uu____13441 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13442 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13441 (rel_to_string (p_rel orig)) uu____13442
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13563 = rhs wl1 scope env1 subst1  in
                     (match uu____13563 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13583 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13583
                            then
                              let uu____13584 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13584
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____13657 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____13657 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___401_13659 = hd1  in
                       let uu____13660 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___401_13659.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___401_13659.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13660
                       }  in
                     let hd21 =
                       let uu___402_13664 = hd2  in
                       let uu____13665 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___402_13664.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___402_13664.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13665
                       }  in
                     let uu____13668 =
                       let uu____13673 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13673
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13668 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13692 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13692
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13696 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13696 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13759 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13759
                                  in
                               ((let uu____13777 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13777
                                 then
                                   let uu____13778 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13779 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13778
                                     uu____13779
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13806 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13839 = aux wl [] env [] bs1 bs2  in
               match uu____13839 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13888 = attempt sub_probs wl2  in
                   solve env uu____13888)

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
            let uu___403_13908 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___403_13908.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___403_13908.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____13916 = try_solve env wl'  in
          match uu____13916 with
          | Success (uu____13917,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___404_13921 = wl  in
                  {
                    attempting = (uu___404_13921.attempting);
                    wl_deferred = (uu___404_13921.wl_deferred);
                    ctr = (uu___404_13921.ctr);
                    defer_ok = (uu___404_13921.defer_ok);
                    smt_ok = (uu___404_13921.smt_ok);
                    umax_heuristic_ok = (uu___404_13921.umax_heuristic_ok);
                    tcenv = (uu___404_13921.tcenv);
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
        (let uu____13929 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13929 wl)

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
              let uu____13943 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13943 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13977 = lhs1  in
              match uu____13977 with
              | (uu____13980,ctx_u,uu____13982) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13990 ->
                        let uu____13991 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13991 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____14038 = quasi_pattern env1 lhs1  in
              match uu____14038 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____14068) ->
                  let uu____14073 = lhs1  in
                  (match uu____14073 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____14087 = occurs_check ctx_u rhs1  in
                       (match uu____14087 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14129 =
                                let uu____14136 =
                                  let uu____14137 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14137
                                   in
                                FStar_Util.Inl uu____14136  in
                              (uu____14129, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14159 =
                                 let uu____14160 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14160  in
                               if uu____14159
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14180 =
                                    let uu____14187 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14187  in
                                  let uu____14192 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14180, uu____14192)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____14235 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14235 with
              | (rhs_hd,args) ->
                  let uu____14278 = FStar_Util.prefix args  in
                  (match uu____14278 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14350 = lhs1  in
                       (match uu____14350 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14354 =
                              let uu____14365 =
                                let uu____14372 =
                                  let uu____14375 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14375
                                   in
                                copy_uvar u_lhs [] uu____14372 wl1  in
                              match uu____14365 with
                              | (uu____14402,t_last_arg,wl2) ->
                                  let uu____14405 =
                                    let uu____14412 =
                                      let uu____14413 =
                                        let uu____14422 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14422]  in
                                      FStar_List.append bs_lhs uu____14413
                                       in
                                    copy_uvar u_lhs uu____14412 t_res_lhs wl2
                                     in
                                  (match uu____14405 with
                                   | (uu____14457,lhs',wl3) ->
                                       let uu____14460 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14460 with
                                        | (uu____14477,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14354 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14498 =
                                     let uu____14499 =
                                       let uu____14504 =
                                         let uu____14505 =
                                           let uu____14508 =
                                             let uu____14513 =
                                               let uu____14514 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14514]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14513
                                              in
                                           uu____14508
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14505
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14504)  in
                                     TERM uu____14499  in
                                   [uu____14498]  in
                                 let uu____14541 =
                                   let uu____14548 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14548 with
                                   | (p1,wl3) ->
                                       let uu____14567 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14567 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14541 with
                                  | (sub_probs,wl3) ->
                                      let uu____14598 =
                                        let uu____14599 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14599  in
                                      solve env1 uu____14598))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14632 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14632 with
                | (uu____14649,args) ->
                    (match args with | [] -> false | uu____14683 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14700 =
                  let uu____14701 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14701.FStar_Syntax_Syntax.n  in
                match uu____14700 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14704 -> true
                | uu____14719 -> false  in
              let uu____14720 = quasi_pattern env1 lhs1  in
              match uu____14720 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14731 =
                    let uu____14732 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14732
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14731
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14739 = is_app rhs1  in
                  if uu____14739
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14741 = is_arrow rhs1  in
                     if uu____14741
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14743 =
                          let uu____14744 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14744
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14743))
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
                let uu____14747 = lhs  in
                (match uu____14747 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14751 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14751 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14768 =
                              let uu____14771 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14771
                               in
                            FStar_All.pipe_right uu____14768
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14788 = occurs_check ctx_uv rhs1  in
                          (match uu____14788 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14810 =
                                   let uu____14811 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14811
                                    in
                                 giveup_or_defer env orig wl uu____14810
                               else
                                 (let uu____14813 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14813
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14818 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14818
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14820 =
                                         let uu____14821 =
                                           names_to_string1 fvs2  in
                                         let uu____14822 =
                                           names_to_string1 fvs1  in
                                         let uu____14823 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14821 uu____14822
                                           uu____14823
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14820)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14831 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14835 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14835 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14858 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14858
                             | (FStar_Util.Inl msg,uu____14860) ->
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
                  (let uu____14893 =
                     let uu____14910 = quasi_pattern env lhs  in
                     let uu____14917 = quasi_pattern env rhs  in
                     (uu____14910, uu____14917)  in
                   match uu____14893 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14960 = lhs  in
                       (match uu____14960 with
                        | ({ FStar_Syntax_Syntax.n = uu____14961;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14963;_},u_lhs,uu____14965)
                            ->
                            let uu____14968 = rhs  in
                            (match uu____14968 with
                             | (uu____14969,u_rhs,uu____14971) ->
                                 let uu____14972 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14972
                                 then
                                   let uu____14977 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14977
                                 else
                                   (let uu____14979 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____14979 with
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
                                        let uu____15011 =
                                          let uu____15018 =
                                            let uu____15021 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____15021
                                             in
                                          new_uvar
                                            (Prims.strcat "flex-flex quasi:"
                                               (Prims.strcat "\tlhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____15018
                                            FStar_Syntax_Syntax.Strict
                                           in
                                        (match uu____15011 with
                                         | (uu____15024,w,wl1) ->
                                             let w_app =
                                               let uu____15030 =
                                                 let uu____15035 =
                                                   FStar_List.map
                                                     (fun uu____15046  ->
                                                        match uu____15046
                                                        with
                                                        | (z,uu____15054) ->
                                                            let uu____15059 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15059) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15035
                                                  in
                                               uu____15030
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____15063 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____15063
                                               then
                                                 let uu____15064 =
                                                   let uu____15067 =
                                                     flex_t_to_string lhs  in
                                                   let uu____15068 =
                                                     let uu____15071 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____15072 =
                                                       let uu____15075 =
                                                         term_to_string w  in
                                                       let uu____15076 =
                                                         let uu____15079 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____15086 =
                                                           let uu____15089 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____15096 =
                                                             let uu____15099
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____15099]
                                                              in
                                                           uu____15089 ::
                                                             uu____15096
                                                            in
                                                         uu____15079 ::
                                                           uu____15086
                                                          in
                                                       uu____15075 ::
                                                         uu____15076
                                                        in
                                                     uu____15071 ::
                                                       uu____15072
                                                      in
                                                   uu____15067 :: uu____15068
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____15064
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____15105 =
                                                     let uu____15110 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____15110)  in
                                                   TERM uu____15105  in
                                                 let uu____15111 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____15111
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____15116 =
                                                        let uu____15121 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____15121)
                                                         in
                                                      TERM uu____15116  in
                                                    [s1; s2])
                                                  in
                                               let uu____15122 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____15122))))))
                   | uu____15123 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____15188 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15188
            then
              let uu____15189 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15190 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15191 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15192 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15189 uu____15190 uu____15191 uu____15192
            else ());
           (let uu____15195 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15195 with
            | (head1,args1) ->
                let uu____15238 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15238 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____15303 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____15303 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15328 =
                         let uu____15329 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15330 = args_to_string args1  in
                         let uu____15333 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15334 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15329 uu____15330 uu____15333 uu____15334
                          in
                       giveup env1 uu____15328 orig
                     else
                       (let uu____15338 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15344 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15344 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15338
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___405_15346 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___405_15346.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___405_15346.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___405_15346.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___405_15346.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___405_15346.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___405_15346.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___405_15346.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___405_15346.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____15353 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____15353
                                    else solve env1 wl2))
                        else
                          (let uu____15356 = base_and_refinement env1 t1  in
                           match uu____15356 with
                           | (base1,refinement1) ->
                               let uu____15381 = base_and_refinement env1 t2
                                  in
                               (match uu____15381 with
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
                                           let uu____15544 =
                                             FStar_List.fold_right
                                               (fun uu____15584  ->
                                                  fun uu____15585  ->
                                                    match (uu____15584,
                                                            uu____15585)
                                                    with
                                                    | (((a1,uu____15637),
                                                        (a2,uu____15639)),
                                                       (probs,wl3)) ->
                                                        let uu____15688 =
                                                          let uu____15695 =
                                                            p_scope orig  in
                                                          mk_problem wl3
                                                            uu____15695 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15688
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____15544 with
                                           | (subprobs,wl3) ->
                                               ((let uu____15733 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____15733
                                                 then
                                                   let uu____15734 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____15734
                                                 else ());
                                                (let uu____15737 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____15737
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
                                                    (let uu____15757 =
                                                       mk_sub_probs wl3  in
                                                     match uu____15757 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____15773 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____15773
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____15781 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____15781))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____15804 =
                                                    mk_sub_probs wl3  in
                                                  match uu____15804 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____15818 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____15818)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____15843 =
                                           match uu____15843 with
                                           | (prob,reason) ->
                                               ((let uu____15851 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____15851
                                                 then
                                                   let uu____15852 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s without SMT because %s"
                                                     uu____15852 reason
                                                 else ());
                                                (let t1' =
                                                   normalize_refinement
                                                     [FStar_TypeChecker_Env.UnfoldUntil
                                                        d;
                                                     FStar_TypeChecker_Env.Weak;
                                                     FStar_TypeChecker_Env.HNF]
                                                     env2 t1
                                                    in
                                                 let t2' =
                                                   normalize_refinement
                                                     [FStar_TypeChecker_Env.UnfoldUntil
                                                        d;
                                                     FStar_TypeChecker_Env.Weak;
                                                     FStar_TypeChecker_Env.HNF]
                                                     env2 t2
                                                    in
                                                 let uu____15856 =
                                                   FStar_Syntax_Util.head_and_args
                                                     t1'
                                                    in
                                                 match uu____15856 with
                                                 | (head1',uu____15874) ->
                                                     let uu____15899 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t2'
                                                        in
                                                     (match uu____15899 with
                                                      | (head2',uu____15917)
                                                          ->
                                                          let uu____15942 =
                                                            let uu____15947 =
                                                              FStar_Syntax_Util.eq_tm
                                                                head1' head1
                                                               in
                                                            let uu____15948 =
                                                              FStar_Syntax_Util.eq_tm
                                                                head2' head2
                                                               in
                                                            (uu____15947,
                                                              uu____15948)
                                                             in
                                                          (match uu____15942
                                                           with
                                                           | (FStar_Syntax_Util.Equal
                                                              ,FStar_Syntax_Util.Equal
                                                              ) ->
                                                               ((let uu____15950
                                                                   =
                                                                   FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                    in
                                                                 if
                                                                   uu____15950
                                                                 then
                                                                   let uu____15951
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                   let uu____15952
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                   let uu____15953
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                   let uu____15954
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                   FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____15951
                                                                    uu____15952
                                                                    uu____15953
                                                                    uu____15954
                                                                 else ());
                                                                solve_sub_probs
                                                                  env2 wl2)
                                                           | uu____15956 ->
                                                               solve_t env2
                                                                 (let uu___406_15962
                                                                    = torig
                                                                     in
                                                                  {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___406_15962.FStar_TypeChecker_Common.rank)
                                                                  }) wl2))))
                                            in
                                         let d =
                                           let uu____15966 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____15966 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         (match d with
                                          | FStar_Pervasives_Native.Some d1
                                              when wl1.smt_ok ->
                                              try_solve_without_smt_or_else
                                                env1 wl1
                                                solve_sub_probs_no_smt
                                                (unfold_and_retry d1)
                                          | uu____15973 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____15976 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___407_16012 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___407_16012.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___407_16012.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___407_16012.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___407_16012.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___407_16012.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___407_16012.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___407_16012.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___407_16012.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16087 = destruct_flex_t scrutinee wl1  in
             match uu____16087 with
             | ((_t,uv,_args),wl2) ->
                 let uu____16098 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____16098 with
                  | (xs,pat_term,uu____16113,uu____16114) ->
                      let uu____16119 =
                        FStar_List.fold_left
                          (fun uu____16142  ->
                             fun x  ->
                               match uu____16142 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____16163 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____16163 with
                                    | (uu____16182,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____16119 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____16203 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____16203 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___408_16219 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___408_16219.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___408_16219.umax_heuristic_ok);
                                    tcenv = (uu___408_16219.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____16227 = solve env1 wl'  in
                                (match uu____16227 with
                                 | Success (uu____16230,imps) ->
                                     let wl'1 =
                                       let uu___409_16233 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___409_16233.wl_deferred);
                                         ctr = (uu___409_16233.ctr);
                                         defer_ok = (uu___409_16233.defer_ok);
                                         smt_ok = (uu___409_16233.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___409_16233.umax_heuristic_ok);
                                         tcenv = (uu___409_16233.tcenv);
                                         wl_implicits =
                                           (uu___409_16233.wl_implicits)
                                       }  in
                                     let uu____16234 = solve env1 wl'1  in
                                     (match uu____16234 with
                                      | Success (uu____16237,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___410_16241 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___410_16241.attempting);
                                                 wl_deferred =
                                                   (uu___410_16241.wl_deferred);
                                                 ctr = (uu___410_16241.ctr);
                                                 defer_ok =
                                                   (uu___410_16241.defer_ok);
                                                 smt_ok =
                                                   (uu___410_16241.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___410_16241.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___410_16241.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16242 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16248 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16269 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16269
                 then
                   let uu____16270 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16271 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16270 uu____16271
                 else ());
                (let uu____16273 =
                   let uu____16294 =
                     let uu____16303 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16303)  in
                   let uu____16310 =
                     let uu____16319 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16319)  in
                   (uu____16294, uu____16310)  in
                 match uu____16273 with
                 | ((uu____16348,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16351;
                                   FStar_Syntax_Syntax.vars = uu____16352;_}),
                    (s,t)) ->
                     let uu____16423 =
                       let uu____16424 = is_flex scrutinee  in
                       Prims.op_Negation uu____16424  in
                     if uu____16423
                     then
                       ((let uu____16432 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16432
                         then
                           let uu____16433 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16433
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16445 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16445
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16451 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16451
                           then
                             let uu____16452 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16453 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16452 uu____16453
                           else ());
                          (let pat_discriminates uu___367_16474 =
                             match uu___367_16474 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16489;
                                  FStar_Syntax_Syntax.p = uu____16490;_},FStar_Pervasives_Native.None
                                ,uu____16491) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16504;
                                  FStar_Syntax_Syntax.p = uu____16505;_},FStar_Pervasives_Native.None
                                ,uu____16506) -> true
                             | uu____16531 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16631 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16631 with
                                       | (uu____16632,uu____16633,t') ->
                                           let uu____16651 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____16651 with
                                            | (FullMatch ,uu____16662) ->
                                                true
                                            | (HeadMatch
                                               uu____16675,uu____16676) ->
                                                true
                                            | uu____16689 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16722 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16722
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16727 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16727 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16815,uu____16816) ->
                                       branches1
                                   | uu____16961 -> branches  in
                                 let uu____17016 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17025 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17025 with
                                        | (p,uu____17029,uu____17030) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____17016))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17086 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17086 with
                                | (p,uu____17094,e) ->
                                    ((let uu____17113 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17113
                                      then
                                        let uu____17114 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17115 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17114 uu____17115
                                      else ());
                                     (let uu____17117 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____17117)))))
                 | ((s,t),(uu____17132,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____17135;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17136;_}))
                     ->
                     let uu____17205 =
                       let uu____17206 = is_flex scrutinee  in
                       Prims.op_Negation uu____17206  in
                     if uu____17205
                     then
                       ((let uu____17214 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____17214
                         then
                           let uu____17215 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17215
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17227 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17227
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17233 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17233
                           then
                             let uu____17234 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____17235 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17234 uu____17235
                           else ());
                          (let pat_discriminates uu___367_17256 =
                             match uu___367_17256 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17271;
                                  FStar_Syntax_Syntax.p = uu____17272;_},FStar_Pervasives_Native.None
                                ,uu____17273) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17286;
                                  FStar_Syntax_Syntax.p = uu____17287;_},FStar_Pervasives_Native.None
                                ,uu____17288) -> true
                             | uu____17313 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17413 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17413 with
                                       | (uu____17414,uu____17415,t') ->
                                           let uu____17433 =
                                             head_matches_delta env1 s t'  in
                                           (match uu____17433 with
                                            | (FullMatch ,uu____17444) ->
                                                true
                                            | (HeadMatch
                                               uu____17457,uu____17458) ->
                                                true
                                            | uu____17471 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17504 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17504
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17509 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17509 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17597,uu____17598) ->
                                       branches1
                                   | uu____17743 -> branches  in
                                 let uu____17798 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17807 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17807 with
                                        | (p,uu____17811,uu____17812) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17798))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17868 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17868 with
                                | (p,uu____17876,e) ->
                                    ((let uu____17895 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17895
                                      then
                                        let uu____17896 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17897 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17896 uu____17897
                                      else ());
                                     (let uu____17899 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17899)))))
                 | uu____17912 ->
                     ((let uu____17934 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17934
                       then
                         let uu____17935 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17936 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17935 uu____17936
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17978 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____17978
            then
              let uu____17979 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17980 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____17981 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17982 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____17979 uu____17980 uu____17981 uu____17982
            else ());
           (let uu____17984 = head_matches_delta env1 t1 t2  in
            match uu____17984 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____18015,uu____18016) ->
                     let rec may_relate head3 =
                       let uu____18043 =
                         let uu____18044 = FStar_Syntax_Subst.compress head3
                            in
                         uu____18044.FStar_Syntax_Syntax.n  in
                       match uu____18043 with
                       | FStar_Syntax_Syntax.Tm_name uu____18047 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18048 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____18072 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____18072 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____18073 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____18074
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____18075 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____18077,uu____18078) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____18120) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____18126) ->
                           may_relate t
                       | uu____18131 -> false  in
                     let uu____18132 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____18132 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____18147 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____18147
                          then
                            let uu____18148 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____18148 with
                             | (guard,wl2) ->
                                 let uu____18155 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____18155)
                          else
                            (let uu____18157 =
                               let uu____18158 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____18159 =
                                 let uu____18160 =
                                   let uu____18163 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____18163
                                     (fun x  ->
                                        let uu____18169 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____18169)
                                    in
                                 FStar_Util.dflt "" uu____18160  in
                               let uu____18170 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____18171 =
                                 let uu____18172 =
                                   let uu____18175 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____18175
                                     (fun x  ->
                                        let uu____18181 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____18181)
                                    in
                                 FStar_Util.dflt "" uu____18172  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____18158 uu____18159 uu____18170
                                 uu____18171
                                in
                             giveup env1 uu____18157 orig))
                 | (HeadMatch (true ),uu____18182) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18195 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____18195 with
                        | (guard,wl2) ->
                            let uu____18202 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____18202)
                     else
                       (let uu____18204 =
                          let uu____18205 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____18206 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____18205 uu____18206
                           in
                        giveup env1 uu____18204 orig)
                 | (uu____18207,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___411_18221 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___411_18221.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___411_18221.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___411_18221.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___411_18221.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___411_18221.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___411_18221.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___411_18221.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___411_18221.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18245 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18245
          then
            let uu____18246 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18246
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18251 =
                let uu____18254 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18254  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18251 t1);
             (let uu____18272 =
                let uu____18275 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18275  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18272 t2);
             (let uu____18293 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18293
              then
                let uu____18294 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18295 =
                  let uu____18296 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18297 =
                    let uu____18298 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18298  in
                  Prims.strcat uu____18296 uu____18297  in
                let uu____18299 =
                  let uu____18300 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18301 =
                    let uu____18302 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18302  in
                  Prims.strcat uu____18300 uu____18301  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18294
                  uu____18295 uu____18299
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18305,uu____18306) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18329,FStar_Syntax_Syntax.Tm_delayed uu____18330) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18353,uu____18354) ->
                  let uu____18381 =
                    let uu___412_18382 = problem  in
                    let uu____18383 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___412_18382.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18383;
                      FStar_TypeChecker_Common.relation =
                        (uu___412_18382.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___412_18382.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___412_18382.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___412_18382.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___412_18382.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___412_18382.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___412_18382.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___412_18382.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18381 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18384,uu____18385) ->
                  let uu____18392 =
                    let uu___413_18393 = problem  in
                    let uu____18394 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___413_18393.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18394;
                      FStar_TypeChecker_Common.relation =
                        (uu___413_18393.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___413_18393.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___413_18393.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___413_18393.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___413_18393.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___413_18393.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___413_18393.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___413_18393.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18392 wl
              | (uu____18395,FStar_Syntax_Syntax.Tm_ascribed uu____18396) ->
                  let uu____18423 =
                    let uu___414_18424 = problem  in
                    let uu____18425 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___414_18424.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___414_18424.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___414_18424.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18425;
                      FStar_TypeChecker_Common.element =
                        (uu___414_18424.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___414_18424.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___414_18424.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___414_18424.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___414_18424.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___414_18424.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18423 wl
              | (uu____18426,FStar_Syntax_Syntax.Tm_meta uu____18427) ->
                  let uu____18434 =
                    let uu___415_18435 = problem  in
                    let uu____18436 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___415_18435.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___415_18435.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___415_18435.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18436;
                      FStar_TypeChecker_Common.element =
                        (uu___415_18435.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___415_18435.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___415_18435.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___415_18435.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___415_18435.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___415_18435.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18434 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18438),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18440)) ->
                  let uu____18449 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18449
              | (FStar_Syntax_Syntax.Tm_bvar uu____18450,uu____18451) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18452,FStar_Syntax_Syntax.Tm_bvar uu____18453) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___368_18522 =
                    match uu___368_18522 with
                    | [] -> c
                    | bs ->
                        let uu____18550 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18550
                     in
                  let uu____18561 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18561 with
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
                                    let uu____18710 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18710
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
                  let mk_t t l uu___369_18795 =
                    match uu___369_18795 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18837 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18837 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____18982 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____18983 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____18982
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____18983 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____18984,uu____18985) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19014 -> true
                    | uu____19033 -> false  in
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
                      (let uu____19086 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___416_19094 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___416_19094.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___416_19094.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___416_19094.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___416_19094.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___416_19094.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___416_19094.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___416_19094.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___416_19094.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___416_19094.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___416_19094.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___416_19094.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___416_19094.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___416_19094.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___416_19094.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___416_19094.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___416_19094.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___416_19094.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___416_19094.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___416_19094.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___416_19094.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___416_19094.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___416_19094.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___416_19094.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___416_19094.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___416_19094.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___416_19094.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___416_19094.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___416_19094.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___416_19094.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___416_19094.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___416_19094.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___416_19094.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___416_19094.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___416_19094.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___416_19094.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___416_19094.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___416_19094.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___416_19094.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___416_19094.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19086 with
                       | (uu____19097,ty,uu____19099) ->
                           let uu____19100 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19100)
                     in
                  let uu____19101 =
                    let uu____19118 = maybe_eta t1  in
                    let uu____19125 = maybe_eta t2  in
                    (uu____19118, uu____19125)  in
                  (match uu____19101 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___417_19167 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___417_19167.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___417_19167.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___417_19167.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___417_19167.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___417_19167.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___417_19167.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___417_19167.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___417_19167.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19188 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19188
                       then
                         let uu____19189 = destruct_flex_t not_abs wl  in
                         (match uu____19189 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___418_19204 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___418_19204.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___418_19204.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___418_19204.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___418_19204.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___418_19204.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___418_19204.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___418_19204.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___418_19204.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19226 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19226
                       then
                         let uu____19227 = destruct_flex_t not_abs wl  in
                         (match uu____19227 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___418_19242 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___418_19242.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___418_19242.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___418_19242.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___418_19242.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___418_19242.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___418_19242.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___418_19242.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___418_19242.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19244 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19261,FStar_Syntax_Syntax.Tm_abs uu____19262) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19291 -> true
                    | uu____19310 -> false  in
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
                      (let uu____19363 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___416_19371 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___416_19371.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___416_19371.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___416_19371.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___416_19371.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___416_19371.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___416_19371.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___416_19371.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___416_19371.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___416_19371.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___416_19371.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___416_19371.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___416_19371.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___416_19371.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___416_19371.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___416_19371.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___416_19371.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___416_19371.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___416_19371.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___416_19371.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___416_19371.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___416_19371.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___416_19371.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___416_19371.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___416_19371.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___416_19371.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___416_19371.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___416_19371.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___416_19371.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___416_19371.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___416_19371.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___416_19371.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___416_19371.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___416_19371.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___416_19371.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___416_19371.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___416_19371.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___416_19371.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___416_19371.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___416_19371.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19363 with
                       | (uu____19374,ty,uu____19376) ->
                           let uu____19377 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19377)
                     in
                  let uu____19378 =
                    let uu____19395 = maybe_eta t1  in
                    let uu____19402 = maybe_eta t2  in
                    (uu____19395, uu____19402)  in
                  (match uu____19378 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___417_19444 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___417_19444.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___417_19444.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___417_19444.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___417_19444.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___417_19444.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___417_19444.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___417_19444.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___417_19444.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19465 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19465
                       then
                         let uu____19466 = destruct_flex_t not_abs wl  in
                         (match uu____19466 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___418_19481 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___418_19481.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___418_19481.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___418_19481.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___418_19481.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___418_19481.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___418_19481.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___418_19481.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___418_19481.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19503 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19503
                       then
                         let uu____19504 = destruct_flex_t not_abs wl  in
                         (match uu____19504 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___418_19519 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___418_19519.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___418_19519.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___418_19519.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___418_19519.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___418_19519.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___418_19519.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___418_19519.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___418_19519.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19521 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19550 =
                    let uu____19555 =
                      head_matches_delta env x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19555 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___419_19583 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___419_19583.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___419_19583.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___420_19585 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___420_19585.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___420_19585.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19586,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___419_19600 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___419_19600.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___419_19600.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___420_19602 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___420_19602.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___420_19602.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19603 -> (x1, x2)  in
                  (match uu____19550 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19622 = as_refinement false env t11  in
                       (match uu____19622 with
                        | (x12,phi11) ->
                            let uu____19629 = as_refinement false env t21  in
                            (match uu____19629 with
                             | (x22,phi21) ->
                                 ((let uu____19637 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19637
                                   then
                                     ((let uu____19639 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19640 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19641 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19639
                                         uu____19640 uu____19641);
                                      (let uu____19642 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19643 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19644 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19642
                                         uu____19643 uu____19644))
                                   else ());
                                  (let uu____19646 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19646 with
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
                                         let uu____19714 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19714
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19726 =
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
                                         (let uu____19737 =
                                            let uu____19740 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19740
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19737
                                            (p_guard base_prob));
                                         (let uu____19758 =
                                            let uu____19761 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19761
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19758
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19779 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19779)
                                          in
                                       let has_uvars =
                                         (let uu____19783 =
                                            let uu____19784 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19784
                                             in
                                          Prims.op_Negation uu____19783) ||
                                           (let uu____19788 =
                                              let uu____19789 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19789
                                               in
                                            Prims.op_Negation uu____19788)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19792 =
                                           let uu____19797 =
                                             let uu____19806 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19806]  in
                                           mk_t_problem wl1 uu____19797 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19792 with
                                          | (ref_prob,wl2) ->
                                              let uu____19827 =
                                                solve env1
                                                  (let uu___421_19829 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___421_19829.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___421_19829.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___421_19829.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___421_19829.tcenv);
                                                     wl_implicits =
                                                       (uu___421_19829.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19827 with
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
                                               | Success uu____19839 ->
                                                   let guard =
                                                     let uu____19847 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19847
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___422_19856 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___422_19856.attempting);
                                                       wl_deferred =
                                                         (uu___422_19856.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___422_19856.defer_ok);
                                                       smt_ok =
                                                         (uu___422_19856.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___422_19856.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___422_19856.tcenv);
                                                       wl_implicits =
                                                         (uu___422_19856.wl_implicits)
                                                     }  in
                                                   let uu____19857 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19857))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19859,FStar_Syntax_Syntax.Tm_uvar uu____19860) ->
                  let uu____19885 = destruct_flex_t t1 wl  in
                  (match uu____19885 with
                   | (f1,wl1) ->
                       let uu____19892 = destruct_flex_t t2 wl1  in
                       (match uu____19892 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19899;
                    FStar_Syntax_Syntax.pos = uu____19900;
                    FStar_Syntax_Syntax.vars = uu____19901;_},uu____19902),FStar_Syntax_Syntax.Tm_uvar
                 uu____19903) ->
                  let uu____19952 = destruct_flex_t t1 wl  in
                  (match uu____19952 with
                   | (f1,wl1) ->
                       let uu____19959 = destruct_flex_t t2 wl1  in
                       (match uu____19959 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19966,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19967;
                    FStar_Syntax_Syntax.pos = uu____19968;
                    FStar_Syntax_Syntax.vars = uu____19969;_},uu____19970))
                  ->
                  let uu____20019 = destruct_flex_t t1 wl  in
                  (match uu____20019 with
                   | (f1,wl1) ->
                       let uu____20026 = destruct_flex_t t2 wl1  in
                       (match uu____20026 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20033;
                    FStar_Syntax_Syntax.pos = uu____20034;
                    FStar_Syntax_Syntax.vars = uu____20035;_},uu____20036),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20037;
                    FStar_Syntax_Syntax.pos = uu____20038;
                    FStar_Syntax_Syntax.vars = uu____20039;_},uu____20040))
                  ->
                  let uu____20113 = destruct_flex_t t1 wl  in
                  (match uu____20113 with
                   | (f1,wl1) ->
                       let uu____20120 = destruct_flex_t t2 wl1  in
                       (match uu____20120 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20127,uu____20128) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20141 = destruct_flex_t t1 wl  in
                  (match uu____20141 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20148;
                    FStar_Syntax_Syntax.pos = uu____20149;
                    FStar_Syntax_Syntax.vars = uu____20150;_},uu____20151),uu____20152)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20189 = destruct_flex_t t1 wl  in
                  (match uu____20189 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____20196,FStar_Syntax_Syntax.Tm_uvar uu____20197) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____20210,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20211;
                    FStar_Syntax_Syntax.pos = uu____20212;
                    FStar_Syntax_Syntax.vars = uu____20213;_},uu____20214))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20251,FStar_Syntax_Syntax.Tm_arrow uu____20252) ->
                  solve_t' env
                    (let uu___423_20280 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___423_20280.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___423_20280.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___423_20280.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___423_20280.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___423_20280.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___423_20280.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___423_20280.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___423_20280.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___423_20280.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20281;
                    FStar_Syntax_Syntax.pos = uu____20282;
                    FStar_Syntax_Syntax.vars = uu____20283;_},uu____20284),FStar_Syntax_Syntax.Tm_arrow
                 uu____20285) ->
                  solve_t' env
                    (let uu___423_20337 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___423_20337.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___423_20337.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___423_20337.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___423_20337.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___423_20337.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___423_20337.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___423_20337.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___423_20337.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___423_20337.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20338,FStar_Syntax_Syntax.Tm_uvar uu____20339) ->
                  let uu____20352 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20352
              | (uu____20353,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20354;
                    FStar_Syntax_Syntax.pos = uu____20355;
                    FStar_Syntax_Syntax.vars = uu____20356;_},uu____20357))
                  ->
                  let uu____20394 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20394
              | (FStar_Syntax_Syntax.Tm_uvar uu____20395,uu____20396) ->
                  let uu____20409 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20409
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20410;
                    FStar_Syntax_Syntax.pos = uu____20411;
                    FStar_Syntax_Syntax.vars = uu____20412;_},uu____20413),uu____20414)
                  ->
                  let uu____20451 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20451
              | (FStar_Syntax_Syntax.Tm_refine uu____20452,uu____20453) ->
                  let t21 =
                    let uu____20461 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20461  in
                  solve_t env
                    (let uu___424_20487 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___424_20487.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___424_20487.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___424_20487.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___424_20487.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___424_20487.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___424_20487.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___424_20487.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___424_20487.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___424_20487.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20488,FStar_Syntax_Syntax.Tm_refine uu____20489) ->
                  let t11 =
                    let uu____20497 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20497  in
                  solve_t env
                    (let uu___425_20523 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___425_20523.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___425_20523.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___425_20523.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___425_20523.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___425_20523.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___425_20523.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___425_20523.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___425_20523.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___425_20523.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20605 =
                    let uu____20606 = guard_of_prob env wl problem t1 t2  in
                    match uu____20606 with
                    | (guard,wl1) ->
                        let uu____20613 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20613
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20824 = br1  in
                        (match uu____20824 with
                         | (p1,w1,uu____20849) ->
                             let uu____20866 = br2  in
                             (match uu____20866 with
                              | (p2,w2,uu____20885) ->
                                  let uu____20890 =
                                    let uu____20891 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20891  in
                                  if uu____20890
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20907 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20907 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____20940 = br2  in
                                         (match uu____20940 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____20977 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____20977
                                                 in
                                              let uu____20990 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____21013,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____21030) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____21073 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____21073 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____20990
                                                (fun uu____21115  ->
                                                   match uu____21115 with
                                                   | (wprobs,wl2) ->
                                                       let uu____21136 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____21136
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____21151 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____21151
                                                              (fun
                                                                 uu____21175 
                                                                 ->
                                                                 match uu____21175
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____21260 -> FStar_Pervasives_Native.None  in
                  let uu____21297 = solve_branches wl brs1 brs2  in
                  (match uu____21297 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21325 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21325 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____21344 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21344  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21353 =
                              let uu____21354 =
                                attempt sub_probs1
                                  (let uu___426_21356 = wl3  in
                                   {
                                     attempting = (uu___426_21356.attempting);
                                     wl_deferred =
                                       (uu___426_21356.wl_deferred);
                                     ctr = (uu___426_21356.ctr);
                                     defer_ok = (uu___426_21356.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___426_21356.umax_heuristic_ok);
                                     tcenv = (uu___426_21356.tcenv);
                                     wl_implicits =
                                       (uu___426_21356.wl_implicits)
                                   })
                                 in
                              solve env uu____21354  in
                            (match uu____21353 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21360 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21366,uu____21367) ->
                  let head1 =
                    let uu____21391 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21391
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21437 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21437
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21483 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21483
                    then
                      let uu____21484 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21485 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21486 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21484 uu____21485 uu____21486
                    else ());
                   (let no_free_uvars t =
                      (let uu____21496 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21496) &&
                        (let uu____21500 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21500)
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
                      let uu____21516 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21516 = FStar_Syntax_Util.Equal  in
                    let uu____21517 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21517
                    then
                      let uu____21518 =
                        let uu____21525 = equal t1 t2  in
                        if uu____21525
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21535 = mk_eq2 wl orig t1 t2  in
                           match uu____21535 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21518 with
                      | (guard,wl1) ->
                          let uu____21556 = solve_prob orig guard [] wl1  in
                          solve env uu____21556
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21558,uu____21559) ->
                  let head1 =
                    let uu____21567 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21567
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21613 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21613
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21659 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21659
                    then
                      let uu____21660 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21661 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21662 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21660 uu____21661 uu____21662
                    else ());
                   (let no_free_uvars t =
                      (let uu____21672 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21672) &&
                        (let uu____21676 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21676)
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
                      let uu____21692 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21692 = FStar_Syntax_Util.Equal  in
                    let uu____21693 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21693
                    then
                      let uu____21694 =
                        let uu____21701 = equal t1 t2  in
                        if uu____21701
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21711 = mk_eq2 wl orig t1 t2  in
                           match uu____21711 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21694 with
                      | (guard,wl1) ->
                          let uu____21732 = solve_prob orig guard [] wl1  in
                          solve env uu____21732
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____21734,uu____21735) ->
                  let head1 =
                    let uu____21737 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21737
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21783 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21783
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21829 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21829
                    then
                      let uu____21830 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21831 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21832 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21830 uu____21831 uu____21832
                    else ());
                   (let no_free_uvars t =
                      (let uu____21842 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21842) &&
                        (let uu____21846 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21846)
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
                      let uu____21862 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21862 = FStar_Syntax_Util.Equal  in
                    let uu____21863 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21863
                    then
                      let uu____21864 =
                        let uu____21871 = equal t1 t2  in
                        if uu____21871
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____21881 = mk_eq2 wl orig t1 t2  in
                           match uu____21881 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____21864 with
                      | (guard,wl1) ->
                          let uu____21902 = solve_prob orig guard [] wl1  in
                          solve env uu____21902
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____21904,uu____21905) ->
                  let head1 =
                    let uu____21907 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21907
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21953 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21953
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21999 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21999
                    then
                      let uu____22000 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22001 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22002 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22000 uu____22001 uu____22002
                    else ());
                   (let no_free_uvars t =
                      (let uu____22012 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22012) &&
                        (let uu____22016 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22016)
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
                      let uu____22032 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22032 = FStar_Syntax_Util.Equal  in
                    let uu____22033 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22033
                    then
                      let uu____22034 =
                        let uu____22041 = equal t1 t2  in
                        if uu____22041
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22051 = mk_eq2 wl orig t1 t2  in
                           match uu____22051 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22034 with
                      | (guard,wl1) ->
                          let uu____22072 = solve_prob orig guard [] wl1  in
                          solve env uu____22072
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____22074,uu____22075) ->
                  let head1 =
                    let uu____22077 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22077
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22123 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22123
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22169 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22169
                    then
                      let uu____22170 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22171 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22172 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22170 uu____22171 uu____22172
                    else ());
                   (let no_free_uvars t =
                      (let uu____22182 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22182) &&
                        (let uu____22186 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22186)
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
                      let uu____22202 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22202 = FStar_Syntax_Util.Equal  in
                    let uu____22203 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22203
                    then
                      let uu____22204 =
                        let uu____22211 = equal t1 t2  in
                        if uu____22211
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22221 = mk_eq2 wl orig t1 t2  in
                           match uu____22221 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22204 with
                      | (guard,wl1) ->
                          let uu____22242 = solve_prob orig guard [] wl1  in
                          solve env uu____22242
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22244,uu____22245) ->
                  let head1 =
                    let uu____22263 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22263
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22309 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22309
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22355 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22355
                    then
                      let uu____22356 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22357 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22358 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22356 uu____22357 uu____22358
                    else ());
                   (let no_free_uvars t =
                      (let uu____22368 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22368) &&
                        (let uu____22372 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22372)
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
                      let uu____22388 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22388 = FStar_Syntax_Util.Equal  in
                    let uu____22389 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22389
                    then
                      let uu____22390 =
                        let uu____22397 = equal t1 t2  in
                        if uu____22397
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22407 = mk_eq2 wl orig t1 t2  in
                           match uu____22407 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22390 with
                      | (guard,wl1) ->
                          let uu____22428 = solve_prob orig guard [] wl1  in
                          solve env uu____22428
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22430,FStar_Syntax_Syntax.Tm_match uu____22431) ->
                  let head1 =
                    let uu____22455 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22455
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22501 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22501
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22547 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22547
                    then
                      let uu____22548 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22549 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22550 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22548 uu____22549 uu____22550
                    else ());
                   (let no_free_uvars t =
                      (let uu____22560 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22560) &&
                        (let uu____22564 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22564)
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
                      let uu____22580 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22580 = FStar_Syntax_Util.Equal  in
                    let uu____22581 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22581
                    then
                      let uu____22582 =
                        let uu____22589 = equal t1 t2  in
                        if uu____22589
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22599 = mk_eq2 wl orig t1 t2  in
                           match uu____22599 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22582 with
                      | (guard,wl1) ->
                          let uu____22620 = solve_prob orig guard [] wl1  in
                          solve env uu____22620
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22622,FStar_Syntax_Syntax.Tm_uinst uu____22623) ->
                  let head1 =
                    let uu____22631 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22631
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22671 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22671
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22711 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22711
                    then
                      let uu____22712 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22713 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22714 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22712 uu____22713 uu____22714
                    else ());
                   (let no_free_uvars t =
                      (let uu____22724 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22724) &&
                        (let uu____22728 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22728)
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
                      let uu____22744 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22744 = FStar_Syntax_Util.Equal  in
                    let uu____22745 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22745
                    then
                      let uu____22746 =
                        let uu____22753 = equal t1 t2  in
                        if uu____22753
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22763 = mk_eq2 wl orig t1 t2  in
                           match uu____22763 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22746 with
                      | (guard,wl1) ->
                          let uu____22784 = solve_prob orig guard [] wl1  in
                          solve env uu____22784
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22786,FStar_Syntax_Syntax.Tm_name uu____22787) ->
                  let head1 =
                    let uu____22789 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22789
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22829 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22829
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22869 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22869
                    then
                      let uu____22870 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22871 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22872 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22870 uu____22871 uu____22872
                    else ());
                   (let no_free_uvars t =
                      (let uu____22882 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22882) &&
                        (let uu____22886 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22886)
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
                      let uu____22902 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22902 = FStar_Syntax_Util.Equal  in
                    let uu____22903 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22903
                    then
                      let uu____22904 =
                        let uu____22911 = equal t1 t2  in
                        if uu____22911
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____22921 = mk_eq2 wl orig t1 t2  in
                           match uu____22921 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____22904 with
                      | (guard,wl1) ->
                          let uu____22942 = solve_prob orig guard [] wl1  in
                          solve env uu____22942
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22944,FStar_Syntax_Syntax.Tm_constant uu____22945) ->
                  let head1 =
                    let uu____22947 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22947
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22987 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22987
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23027 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23027
                    then
                      let uu____23028 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23029 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23030 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23028 uu____23029 uu____23030
                    else ());
                   (let no_free_uvars t =
                      (let uu____23040 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23040) &&
                        (let uu____23044 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23044)
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
                      let uu____23060 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23060 = FStar_Syntax_Util.Equal  in
                    let uu____23061 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23061
                    then
                      let uu____23062 =
                        let uu____23069 = equal t1 t2  in
                        if uu____23069
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23079 = mk_eq2 wl orig t1 t2  in
                           match uu____23079 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23062 with
                      | (guard,wl1) ->
                          let uu____23100 = solve_prob orig guard [] wl1  in
                          solve env uu____23100
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23102,FStar_Syntax_Syntax.Tm_fvar uu____23103) ->
                  let head1 =
                    let uu____23105 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23105
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23151 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23151
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23197 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23197
                    then
                      let uu____23198 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23199 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23200 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23198 uu____23199 uu____23200
                    else ());
                   (let no_free_uvars t =
                      (let uu____23210 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23210) &&
                        (let uu____23214 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23214)
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
                      let uu____23230 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23230 = FStar_Syntax_Util.Equal  in
                    let uu____23231 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23231
                    then
                      let uu____23232 =
                        let uu____23239 = equal t1 t2  in
                        if uu____23239
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23249 = mk_eq2 wl orig t1 t2  in
                           match uu____23249 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23232 with
                      | (guard,wl1) ->
                          let uu____23270 = solve_prob orig guard [] wl1  in
                          solve env uu____23270
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23272,FStar_Syntax_Syntax.Tm_app uu____23273) ->
                  let head1 =
                    let uu____23291 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23291
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23331 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23331
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23371 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23371
                    then
                      let uu____23372 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23373 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23374 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23372 uu____23373 uu____23374
                    else ());
                   (let no_free_uvars t =
                      (let uu____23384 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23384) &&
                        (let uu____23388 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23388)
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
                      let uu____23404 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23404 = FStar_Syntax_Util.Equal  in
                    let uu____23405 =
                      (((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                            (FStar_TypeChecker_Env.is_interpreted env head2))
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ))
                          && wl.smt_ok)
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23405
                    then
                      let uu____23406 =
                        let uu____23413 = equal t1 t2  in
                        if uu____23413
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu____23423 = mk_eq2 wl orig t1 t2  in
                           match uu____23423 with
                           | (g,wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1))
                         in
                      match uu____23406 with
                      | (guard,wl1) ->
                          let uu____23444 = solve_prob orig guard [] wl1  in
                          solve env uu____23444
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23446,FStar_Syntax_Syntax.Tm_let uu____23447) ->
                  let uu____23472 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23472
                  then
                    let uu____23473 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23473
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23475,uu____23476) ->
                  let uu____23489 =
                    let uu____23494 =
                      let uu____23495 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23496 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23497 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23498 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23495 uu____23496 uu____23497 uu____23498
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23494)
                     in
                  FStar_Errors.raise_error uu____23489
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23499,FStar_Syntax_Syntax.Tm_let uu____23500) ->
                  let uu____23513 =
                    let uu____23518 =
                      let uu____23519 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23520 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23521 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23522 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23519 uu____23520 uu____23521 uu____23522
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23518)
                     in
                  FStar_Errors.raise_error uu____23513
                    t1.FStar_Syntax_Syntax.pos
              | uu____23523 -> giveup env "head tag mismatch" orig))))

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
          (let uu____23584 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23584
           then
             let uu____23585 =
               let uu____23586 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23586  in
             let uu____23587 =
               let uu____23588 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23588  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23585 uu____23587
           else ());
          (let uu____23590 =
             let uu____23591 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23591  in
           if uu____23590
           then
             let uu____23592 =
               let uu____23593 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23594 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23593 uu____23594
                in
             giveup env uu____23592 orig
           else
             (let uu____23596 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23596 with
              | (ret_sub_prob,wl1) ->
                  let uu____23603 =
                    FStar_List.fold_right2
                      (fun uu____23640  ->
                         fun uu____23641  ->
                           fun uu____23642  ->
                             match (uu____23640, uu____23641, uu____23642)
                             with
                             | ((a1,uu____23686),(a2,uu____23688),(arg_sub_probs,wl2))
                                 ->
                                 let uu____23721 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____23721 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23603 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____23750 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____23750  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____23758 = attempt sub_probs wl3  in
                       solve env uu____23758)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____23781 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____23784)::[] -> wp1
              | uu____23809 ->
                  let uu____23820 =
                    let uu____23821 =
                      let uu____23822 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____23822  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23821
                     in
                  failwith uu____23820
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____23828 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____23828]
              | x -> x  in
            let uu____23830 =
              let uu____23841 =
                let uu____23850 =
                  let uu____23851 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____23851 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____23850  in
              [uu____23841]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23830;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23868 = lift_c1 ()  in solve_eq uu____23868 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___370_23874  ->
                       match uu___370_23874 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23875 -> false))
                in
             let uu____23876 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23906)::uu____23907,(wp2,uu____23909)::uu____23910)
                   -> (wp1, wp2)
               | uu____23983 ->
                   let uu____24008 =
                     let uu____24013 =
                       let uu____24014 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____24015 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____24014 uu____24015
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____24013)
                      in
                   FStar_Errors.raise_error uu____24008
                     env.FStar_TypeChecker_Env.range
                in
             match uu____23876 with
             | (wpc1,wpc2) ->
                 let uu____24022 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____24022
                 then
                   let uu____24025 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____24025 wl
                 else
                   (let uu____24027 =
                      let uu____24034 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____24034  in
                    match uu____24027 with
                    | (c2_decl,qualifiers) ->
                        let uu____24055 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____24055
                        then
                          let c1_repr =
                            let uu____24059 =
                              let uu____24060 =
                                let uu____24061 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____24061  in
                              let uu____24062 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24060 uu____24062
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24059
                             in
                          let c2_repr =
                            let uu____24064 =
                              let uu____24065 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____24066 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24065 uu____24066
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24064
                             in
                          let uu____24067 =
                            let uu____24072 =
                              let uu____24073 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____24074 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____24073 uu____24074
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____24072
                             in
                          (match uu____24067 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____24078 = attempt [prob] wl2  in
                               solve env uu____24078)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____24089 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24089
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____24092 =
                                     let uu____24099 =
                                       let uu____24100 =
                                         let uu____24117 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____24120 =
                                           let uu____24131 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____24140 =
                                             let uu____24151 =
                                               let uu____24160 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____24160
                                                in
                                             [uu____24151]  in
                                           uu____24131 :: uu____24140  in
                                         (uu____24117, uu____24120)  in
                                       FStar_Syntax_Syntax.Tm_app uu____24100
                                        in
                                     FStar_Syntax_Syntax.mk uu____24099  in
                                   uu____24092 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____24211 =
                                    let uu____24218 =
                                      let uu____24219 =
                                        let uu____24236 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____24239 =
                                          let uu____24250 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24259 =
                                            let uu____24270 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24279 =
                                              let uu____24290 =
                                                let uu____24299 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24299
                                                 in
                                              [uu____24290]  in
                                            uu____24270 :: uu____24279  in
                                          uu____24250 :: uu____24259  in
                                        (uu____24236, uu____24239)  in
                                      FStar_Syntax_Syntax.Tm_app uu____24219
                                       in
                                    FStar_Syntax_Syntax.mk uu____24218  in
                                  uu____24211 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24356 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24356
                            then
                              let uu____24357 =
                                let uu____24358 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24358
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24357
                            else ());
                           (let uu____24360 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24360 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24368 =
                                    let uu____24371 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24371
                                     in
                                  solve_prob orig uu____24368 [] wl1  in
                                let uu____24374 = attempt [base_prob] wl2  in
                                solve env uu____24374))))
           in
        let uu____24375 = FStar_Util.physical_equality c1 c2  in
        if uu____24375
        then
          let uu____24376 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24376
        else
          ((let uu____24379 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24379
            then
              let uu____24380 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24381 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24380
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24381
            else ());
           (let uu____24383 =
              let uu____24392 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24395 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24392, uu____24395)  in
            match uu____24383 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24413),FStar_Syntax_Syntax.Total
                    (t2,uu____24415)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24432 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24432 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24433,FStar_Syntax_Syntax.Total uu____24434) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24452),FStar_Syntax_Syntax.Total
                    (t2,uu____24454)) ->
                     let uu____24471 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24471 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24473),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24475)) ->
                     let uu____24492 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24492 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24494),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24496)) ->
                     let uu____24513 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24513 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24514,FStar_Syntax_Syntax.Comp uu____24515) ->
                     let uu____24524 =
                       let uu___427_24527 = problem  in
                       let uu____24530 =
                         let uu____24531 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24531
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___427_24527.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24530;
                         FStar_TypeChecker_Common.relation =
                           (uu___427_24527.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___427_24527.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___427_24527.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___427_24527.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___427_24527.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___427_24527.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___427_24527.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___427_24527.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24524 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24532,FStar_Syntax_Syntax.Comp uu____24533) ->
                     let uu____24542 =
                       let uu___427_24545 = problem  in
                       let uu____24548 =
                         let uu____24549 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24549
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___427_24545.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24548;
                         FStar_TypeChecker_Common.relation =
                           (uu___427_24545.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___427_24545.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___427_24545.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___427_24545.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___427_24545.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___427_24545.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___427_24545.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___427_24545.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24542 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24550,FStar_Syntax_Syntax.GTotal uu____24551) ->
                     let uu____24560 =
                       let uu___428_24563 = problem  in
                       let uu____24566 =
                         let uu____24567 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24567
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___428_24563.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___428_24563.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___428_24563.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24566;
                         FStar_TypeChecker_Common.element =
                           (uu___428_24563.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___428_24563.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___428_24563.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___428_24563.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___428_24563.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___428_24563.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24560 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24568,FStar_Syntax_Syntax.Total uu____24569) ->
                     let uu____24578 =
                       let uu___428_24581 = problem  in
                       let uu____24584 =
                         let uu____24585 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24585
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___428_24581.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___428_24581.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___428_24581.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24584;
                         FStar_TypeChecker_Common.element =
                           (uu___428_24581.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___428_24581.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___428_24581.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___428_24581.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___428_24581.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___428_24581.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24578 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24586,FStar_Syntax_Syntax.Comp uu____24587) ->
                     let uu____24588 =
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
                     if uu____24588
                     then
                       let uu____24589 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24589 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24593 =
                            let uu____24598 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24598
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24604 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24605 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24604, uu____24605))
                             in
                          match uu____24593 with
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
                           (let uu____24612 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24612
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24614 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24614 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24617 =
                                  let uu____24618 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24619 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24618 uu____24619
                                   in
                                giveup env uu____24617 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24626 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24626 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24667 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24667 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24685 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____24713  ->
                match uu____24713 with
                | (u1,u2) ->
                    let uu____24720 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____24721 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____24720 uu____24721))
         in
      FStar_All.pipe_right uu____24685 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____24748,[])) when
          let uu____24773 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____24773 -> "{}"
      | uu____24774 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____24797 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____24797
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____24800 =
              FStar_List.map
                (fun uu____24810  ->
                   match uu____24810 with
                   | (uu____24815,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____24800 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____24820 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____24820 imps
  
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
                  let uu____24873 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____24873
                  then
                    let uu____24874 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____24875 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24874
                      (rel_to_string rel) uu____24875
                  else "TOP"  in
                let uu____24877 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____24877 with
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
              let uu____24935 =
                let uu____24938 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____24938
                 in
              FStar_Syntax_Syntax.new_bv uu____24935 t1  in
            let uu____24941 =
              let uu____24946 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____24946
               in
            match uu____24941 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____25019 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____25019
              then
                let uu____25020 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____25020
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
          ((let uu____25042 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____25042
            then
              let uu____25043 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____25043
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____25047 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____25047
             then
               let uu____25048 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____25048
             else ());
            (let f2 =
               let uu____25051 =
                 let uu____25052 = FStar_Syntax_Util.unmeta f1  in
                 uu____25052.FStar_Syntax_Syntax.n  in
               match uu____25051 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____25056 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___429_25057 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___429_25057.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___429_25057.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___429_25057.FStar_TypeChecker_Env.implicits)
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
            let uu____25111 =
              let uu____25112 =
                let uu____25113 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____25113;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____25112  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____25111
  
let with_guard_no_simp :
  'Auu____25128 .
    'Auu____25128 ->
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
            let uu____25151 =
              let uu____25152 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____25152;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____25151
  
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
          (let uu____25182 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____25182
           then
             let uu____25183 = FStar_Syntax_Print.term_to_string t1  in
             let uu____25184 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____25183
               uu____25184
           else ());
          (let uu____25186 =
             let uu____25191 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____25191
              in
           match uu____25186 with
           | (prob,wl) ->
               let g =
                 let uu____25199 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____25209  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____25199  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25243 = try_teq true env t1 t2  in
        match uu____25243 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25247 = FStar_TypeChecker_Env.get_range env  in
              let uu____25248 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25247 uu____25248);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25255 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25255
              then
                let uu____25256 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25257 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25258 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25256
                  uu____25257 uu____25258
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
          let uu____25280 = FStar_TypeChecker_Env.get_range env  in
          let uu____25281 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25280 uu____25281
  
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
        (let uu____25306 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25306
         then
           let uu____25307 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25308 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25307 uu____25308
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25311 =
           let uu____25318 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25318 "sub_comp"
            in
         match uu____25311 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25329 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25339  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25329)))
  
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
      fun uu____25384  ->
        match uu____25384 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25427 =
                 let uu____25432 =
                   let uu____25433 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25434 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25433 uu____25434
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25432)  in
               let uu____25435 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25427 uu____25435)
               in
            let equiv1 v1 v' =
              let uu____25447 =
                let uu____25452 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25453 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25452, uu____25453)  in
              match uu____25447 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25472 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25502 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25502 with
                      | FStar_Syntax_Syntax.U_unif uu____25509 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25538  ->
                                    match uu____25538 with
                                    | (u,v') ->
                                        let uu____25547 = equiv1 v1 v'  in
                                        if uu____25547
                                        then
                                          let uu____25550 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25550 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25566 -> []))
               in
            let uu____25571 =
              let wl =
                let uu___430_25575 = empty_worklist env  in
                {
                  attempting = (uu___430_25575.attempting);
                  wl_deferred = (uu___430_25575.wl_deferred);
                  ctr = (uu___430_25575.ctr);
                  defer_ok = false;
                  smt_ok = (uu___430_25575.smt_ok);
                  umax_heuristic_ok = (uu___430_25575.umax_heuristic_ok);
                  tcenv = (uu___430_25575.tcenv);
                  wl_implicits = (uu___430_25575.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25593  ->
                      match uu____25593 with
                      | (lb,v1) ->
                          let uu____25600 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25600 with
                           | USolved wl1 -> ()
                           | uu____25602 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25612 =
              match uu____25612 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25621) -> true
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
                      uu____25644,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25646,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25657) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25664,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25672 -> false)
               in
            let uu____25677 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25692  ->
                      match uu____25692 with
                      | (u,v1) ->
                          let uu____25699 = check_ineq (u, v1)  in
                          if uu____25699
                          then true
                          else
                            ((let uu____25702 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____25702
                              then
                                let uu____25703 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____25704 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____25703
                                  uu____25704
                              else ());
                             false)))
               in
            if uu____25677
            then ()
            else
              ((let uu____25708 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____25708
                then
                  ((let uu____25710 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____25710);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____25720 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____25720))
                else ());
               (let uu____25730 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____25730))
  
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
        let fail1 uu____25797 =
          match uu____25797 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___431_25818 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___431_25818.attempting);
            wl_deferred = (uu___431_25818.wl_deferred);
            ctr = (uu___431_25818.ctr);
            defer_ok;
            smt_ok = (uu___431_25818.smt_ok);
            umax_heuristic_ok = (uu___431_25818.umax_heuristic_ok);
            tcenv = (uu___431_25818.tcenv);
            wl_implicits = (uu___431_25818.wl_implicits)
          }  in
        (let uu____25820 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25820
         then
           let uu____25821 = FStar_Util.string_of_bool defer_ok  in
           let uu____25822 = wl_to_string wl  in
           let uu____25823 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____25821 uu____25822 uu____25823
         else ());
        (let g1 =
           let uu____25826 = solve_and_commit env wl fail1  in
           match uu____25826 with
           | FStar_Pervasives_Native.Some
               (uu____25833::uu____25834,uu____25835) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___432_25860 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___432_25860.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___432_25860.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____25861 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___433_25869 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___433_25869.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___433_25869.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___433_25869.FStar_TypeChecker_Env.implicits)
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
    let uu____25917 = FStar_ST.op_Bang last_proof_ns  in
    match uu____25917 with
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
            let uu___434_26028 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___434_26028.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___434_26028.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___434_26028.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____26029 =
            let uu____26030 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____26030  in
          if uu____26029
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____26038 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____26039 =
                       let uu____26040 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____26040
                        in
                     FStar_Errors.diag uu____26038 uu____26039)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____26044 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____26045 =
                        let uu____26046 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____26046
                         in
                      FStar_Errors.diag uu____26044 uu____26045)
                   else ();
                   (let uu____26049 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____26049
                      "discharge_guard'" env vc1);
                   (let uu____26050 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____26050 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____26057 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26058 =
                                let uu____26059 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____26059
                                 in
                              FStar_Errors.diag uu____26057 uu____26058)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____26064 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26065 =
                                let uu____26066 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____26066
                                 in
                              FStar_Errors.diag uu____26064 uu____26065)
                           else ();
                           (let vcs =
                              let uu____26077 = FStar_Options.use_tactics ()
                                 in
                              if uu____26077
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____26097  ->
                                     (let uu____26099 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a236  -> ())
                                        uu____26099);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____26142  ->
                                              match uu____26142 with
                                              | (env1,goal,opts) ->
                                                  let uu____26158 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____26158, opts)))))
                              else
                                (let uu____26160 =
                                   let uu____26167 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____26167)  in
                                 [uu____26160])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____26200  ->
                                    match uu____26200 with
                                    | (env1,goal,opts) ->
                                        let uu____26210 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____26210 with
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
                                                (let uu____26218 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26219 =
                                                   let uu____26220 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____26221 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____26220 uu____26221
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26218 uu____26219)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____26224 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26225 =
                                                   let uu____26226 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____26226
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26224 uu____26225)
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
      let uu____26240 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26240 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26247 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26247
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26258 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26258 with
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
        let uu____26284 = try_teq false env t1 t2  in
        match uu____26284 with
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
            let uu____26319 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26319 with
            | FStar_Pervasives_Native.Some uu____26322 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26342 = acc  in
            match uu____26342 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26354 = hd1  in
                     (match uu____26354 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26359;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26367 = unresolved ctx_u  in
                             if uu____26367
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
                                     let uu____26382 = teq_nosmt env1 t tm
                                        in
                                     match uu____26382 with
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "resolve_implicits: unifying with an unresolved uvar failed?"
                                     | FStar_Pervasives_Native.Some g1 ->
                                         g1.FStar_TypeChecker_Env.implicits
                                      in
                                   let hd2 =
                                     let uu___435_26391 = hd1  in
                                     {
                                       FStar_TypeChecker_Env.imp_reason =
                                         (uu___435_26391.FStar_TypeChecker_Env.imp_reason);
                                       FStar_TypeChecker_Env.imp_uvar =
                                         (uu___435_26391.FStar_TypeChecker_Env.imp_uvar);
                                       FStar_TypeChecker_Env.imp_tm =
                                         (uu___435_26391.FStar_TypeChecker_Env.imp_tm);
                                       FStar_TypeChecker_Env.imp_range =
                                         (uu___435_26391.FStar_TypeChecker_Env.imp_range);
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
                                    let uu___436_26399 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___436_26399.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___436_26399.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___436_26399.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___436_26399.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___436_26399.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___436_26399.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___436_26399.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___436_26399.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___436_26399.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___436_26399.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___436_26399.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___436_26399.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___436_26399.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___436_26399.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___436_26399.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___436_26399.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___436_26399.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___436_26399.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___436_26399.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___436_26399.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___436_26399.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___436_26399.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___436_26399.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___436_26399.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___436_26399.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___436_26399.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___436_26399.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___436_26399.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___436_26399.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___436_26399.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___436_26399.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___436_26399.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___436_26399.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___436_26399.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___436_26399.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___436_26399.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___436_26399.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___436_26399.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___436_26399.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___436_26399.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___436_26399.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___437_26402 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___437_26402.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___437_26402.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___437_26402.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___437_26402.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___437_26402.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___437_26402.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___437_26402.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___437_26402.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___437_26402.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___437_26402.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___437_26402.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___437_26402.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___437_26402.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___437_26402.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___437_26402.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___437_26402.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___437_26402.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___437_26402.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___437_26402.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___437_26402.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___437_26402.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___437_26402.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___437_26402.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___437_26402.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___437_26402.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___437_26402.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___437_26402.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___437_26402.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___437_26402.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___437_26402.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___437_26402.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___437_26402.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___437_26402.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___437_26402.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___437_26402.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___437_26402.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___437_26402.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___437_26402.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___437_26402.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___437_26402.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___437_26402.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26405 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26405
                                   then
                                     let uu____26406 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26407 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26408 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26409 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26406 uu____26407 uu____26408
                                       reason uu____26409
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___439_26413  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26420 =
                                             let uu____26429 =
                                               let uu____26436 =
                                                 let uu____26437 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26438 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26439 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26437 uu____26438
                                                   uu____26439
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26436, r)
                                                in
                                             [uu____26429]  in
                                           FStar_Errors.add_errors
                                             uu____26420);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___440_26453 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___440_26453.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___440_26453.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___440_26453.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26456 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26466  ->
                                               let uu____26467 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26468 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26469 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26467 uu____26468
                                                 reason uu____26469)) env2 g2
                                         true
                                        in
                                     match uu____26456 with
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
          let uu___441_26471 = g  in
          let uu____26472 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___441_26471.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___441_26471.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___441_26471.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26472
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
        let uu____26506 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26506 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26507 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a237  -> ()) uu____26507
      | imp::uu____26509 ->
          let uu____26512 =
            let uu____26517 =
              let uu____26518 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26519 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26518 uu____26519 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26517)
             in
          FStar_Errors.raise_error uu____26512
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26535 = teq_nosmt env t1 t2  in
        match uu____26535 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___442_26550 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___442_26550.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___442_26550.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___442_26550.FStar_TypeChecker_Env.implicits)
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
        (let uu____26585 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26585
         then
           let uu____26586 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26587 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26586
             uu____26587
         else ());
        (let uu____26589 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26589 with
         | (prob,x,wl) ->
             let g =
               let uu____26608 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26618  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26608  in
             ((let uu____26638 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26638
               then
                 let uu____26639 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26640 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26641 =
                   let uu____26642 = FStar_Util.must g  in
                   guard_to_string env uu____26642  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26639 uu____26640 uu____26641
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
        let uu____26676 = check_subtyping env t1 t2  in
        match uu____26676 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26695 =
              let uu____26696 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____26696 g  in
            FStar_Pervasives_Native.Some uu____26695
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26714 = check_subtyping env t1 t2  in
        match uu____26714 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____26733 =
              let uu____26734 =
                let uu____26735 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____26735]  in
              FStar_TypeChecker_Env.close_guard env uu____26734 g  in
            FStar_Pervasives_Native.Some uu____26733
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26772 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26772
         then
           let uu____26773 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26774 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26773
             uu____26774
         else ());
        (let uu____26776 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26776 with
         | (prob,x,wl) ->
             let g =
               let uu____26791 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____26801  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26791  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____26824 =
                      let uu____26825 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____26825]  in
                    FStar_TypeChecker_Env.close_guard env uu____26824 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26862 = subtype_nosmt env t1 t2  in
        match uu____26862 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  