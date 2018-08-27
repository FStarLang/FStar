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
                   (let uu___346_423 = wl  in
                    {
                      attempting = (uu___346_423.attempting);
                      wl_deferred = (uu___346_423.wl_deferred);
                      ctr = (uu___346_423.ctr);
                      defer_ok = (uu___346_423.defer_ok);
                      smt_ok = (uu___346_423.smt_ok);
                      umax_heuristic_ok = (uu___346_423.umax_heuristic_ok);
                      tcenv = (uu___346_423.tcenv);
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
            let uu___347_455 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___347_455.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___347_455.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___347_455.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___347_455.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___347_455.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___347_455.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___347_455.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___347_455.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___347_455.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___347_455.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___347_455.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___347_455.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___347_455.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___347_455.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___347_455.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___347_455.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___347_455.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___347_455.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___347_455.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___347_455.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___347_455.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___347_455.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___347_455.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___347_455.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___347_455.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___347_455.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___347_455.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___347_455.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___347_455.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___347_455.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___347_455.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___347_455.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___347_455.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___347_455.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___347_455.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___347_455.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___347_455.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___347_455.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___347_455.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___347_455.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___347_455.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___347_455.FStar_TypeChecker_Env.nbe)
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
  fun uu___314_576  ->
    match uu___314_576 with
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
    fun uu___315_671  ->
      match uu___315_671 with
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
    fun uu___316_705  ->
      match uu___316_705 with
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
  fun uu___317_843  ->
    match uu___317_843 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____848 .
    'Auu____848 FStar_TypeChecker_Common.problem ->
      'Auu____848 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___348_860 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___348_860.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___348_860.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___348_860.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___348_860.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___348_860.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___348_860.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___348_860.FStar_TypeChecker_Common.rank)
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
  fun uu___318_884  ->
    match uu___318_884 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___319_899  ->
    match uu___319_899 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___349_905 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___349_905.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___349_905.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___349_905.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___349_905.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___349_905.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___349_905.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___349_905.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___349_905.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___349_905.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___350_913 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___350_913.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___350_913.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___350_913.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___350_913.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___350_913.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___350_913.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___350_913.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___350_913.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___350_913.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___320_925  ->
      match uu___320_925 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___321_930  ->
    match uu___321_930 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___322_941  ->
    match uu___322_941 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___323_954  ->
    match uu___323_954 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___324_967  ->
    match uu___324_967 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___325_980  ->
    match uu___325_980 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___326_993  ->
    match uu___326_993 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___327_1004  ->
    match uu___327_1004 with
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
        let uu___351_1373 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___351_1373.wl_deferred);
          ctr = (uu___351_1373.ctr);
          defer_ok = (uu___351_1373.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___351_1373.umax_heuristic_ok);
          tcenv = (uu___351_1373.tcenv);
          wl_implicits = (uu___351_1373.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1380 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1380,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___352_1403 = empty_worklist env  in
      let uu____1404 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1404;
        wl_deferred = (uu___352_1403.wl_deferred);
        ctr = (uu___352_1403.ctr);
        defer_ok = (uu___352_1403.defer_ok);
        smt_ok = (uu___352_1403.smt_ok);
        umax_heuristic_ok = (uu___352_1403.umax_heuristic_ok);
        tcenv = (uu___352_1403.tcenv);
        wl_implicits = (uu___352_1403.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___353_1424 = wl  in
        {
          attempting = (uu___353_1424.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___353_1424.ctr);
          defer_ok = (uu___353_1424.defer_ok);
          smt_ok = (uu___353_1424.smt_ok);
          umax_heuristic_ok = (uu___353_1424.umax_heuristic_ok);
          tcenv = (uu___353_1424.tcenv);
          wl_implicits = (uu___353_1424.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___354_1446 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___354_1446.wl_deferred);
         ctr = (uu___354_1446.ctr);
         defer_ok = (uu___354_1446.defer_ok);
         smt_ok = (uu___354_1446.smt_ok);
         umax_heuristic_ok = (uu___354_1446.umax_heuristic_ok);
         tcenv = (uu___354_1446.tcenv);
         wl_implicits = (uu___354_1446.wl_implicits)
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
  fun uu___328_1517  ->
    match uu___328_1517 with
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
                      (let uu___355_2107 = wl  in
                       {
                         attempting = (uu___355_2107.attempting);
                         wl_deferred = (uu___355_2107.wl_deferred);
                         ctr = (uu___355_2107.ctr);
                         defer_ok = (uu___355_2107.defer_ok);
                         smt_ok = (uu___355_2107.smt_ok);
                         umax_heuristic_ok =
                           (uu___355_2107.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___355_2107.wl_implicits)
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
         (fun uu___329_2328  ->
            match uu___329_2328 with
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
        (fun uu___330_2373  ->
           match uu___330_2373 with
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
        (fun uu___331_2407  ->
           match uu___331_2407 with
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
                    let uu___356_2542 = x  in
                    let uu____2543 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___356_2542.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___356_2542.FStar_Syntax_Syntax.index);
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
                      (fun uu___332_3912  ->
                         match uu___332_3912 with
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
                          (fun uu___333_3958  ->
                             match uu___333_3958 with
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
                               (fun uu___334_4024  ->
                                  match uu___334_4024 with
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
             (let uu___357_4779 = wl1  in
              {
                attempting = (uu___357_4779.attempting);
                wl_deferred = (uu___357_4779.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___357_4779.defer_ok);
                smt_ok = (uu___357_4779.smt_ok);
                umax_heuristic_ok = (uu___357_4779.umax_heuristic_ok);
                tcenv = (uu___357_4779.tcenv);
                wl_implicits = (uu___357_4779.wl_implicits)
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
        (let uu___358_4810 = wl  in
         {
           attempting = (uu___358_4810.attempting);
           wl_deferred = (uu___358_4810.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___358_4810.defer_ok);
           smt_ok = (uu___358_4810.smt_ok);
           umax_heuristic_ok = (uu___358_4810.umax_heuristic_ok);
           tcenv = (uu___358_4810.tcenv);
           wl_implicits = (uu___358_4810.wl_implicits)
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
              (fun uu___335_5297  ->
                 match uu___335_5297 with
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
  fun uu___336_6221  ->
    match uu___336_6221 with
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
  fun uu___337_6243  ->
    match uu___337_6243 with
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
            (let uu____6992 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____6992
             then
               let uu____6993 = FStar_Syntax_Print.term_to_string t  in
               let uu____6994 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____6993 uu____6994
             else ());
            (let uu____6996 =
               let uu____6997 = FStar_Syntax_Util.un_uinst head1  in
               uu____6997.FStar_Syntax_Syntax.n  in
             match uu____6996 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7003 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7003 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7017 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7017
                        then
                          let uu____7018 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7018
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7020 ->
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
                      let uu____7035 =
                        let uu____7036 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7036 = FStar_Syntax_Util.Equal  in
                      if uu____7035
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7041 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7041
                          then
                            let uu____7042 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7043 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7042
                              uu____7043
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7045 -> FStar_Pervasives_Native.None)
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
            (let uu____7183 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7183
             then
               let uu____7184 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7185 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7186 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7184
                 uu____7185 uu____7186
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7210 =
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
               match uu____7210 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7255 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7255 with
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
                  uu____7287),uu____7288)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7306 =
                      let uu____7315 = maybe_inline t11  in
                      let uu____7318 = maybe_inline t21  in
                      (uu____7315, uu____7318)  in
                    match uu____7306 with
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
                 (uu____7355,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7356))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7374 =
                      let uu____7383 = maybe_inline t11  in
                      let uu____7386 = maybe_inline t21  in
                      (uu____7383, uu____7386)  in
                    match uu____7374 with
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
             | MisMatch uu____7435 -> fail1 n_delta r t11 t21
             | uu____7444 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7457 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7457
           then
             let uu____7458 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7459 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7460 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7467 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____7479 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7479
                    (fun uu____7513  ->
                       match uu____7513 with
                       | (t11,t21) ->
                           let uu____7520 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7521 =
                             let uu____7522 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7522  in
                           Prims.strcat uu____7520 uu____7521))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7458 uu____7459 uu____7460 uu____7467
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7534 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7534 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___338_7547  ->
    match uu___338_7547 with
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
      let uu___359_7584 = p  in
      let uu____7587 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7588 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___359_7584.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7587;
        FStar_TypeChecker_Common.relation =
          (uu___359_7584.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7588;
        FStar_TypeChecker_Common.element =
          (uu___359_7584.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___359_7584.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___359_7584.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___359_7584.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___359_7584.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___359_7584.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7602 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7602
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7607 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7629 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7629 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7637 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7637 with
           | (lh,lhs_args) ->
               let uu____7684 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7684 with
                | (rh,rhs_args) ->
                    let uu____7731 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7744,FStar_Syntax_Syntax.Tm_uvar uu____7745)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7834 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7861,uu____7862)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7877,FStar_Syntax_Syntax.Tm_uvar uu____7878)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7893,FStar_Syntax_Syntax.Tm_arrow uu____7894)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___360_7924 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___360_7924.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___360_7924.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___360_7924.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___360_7924.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___360_7924.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___360_7924.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___360_7924.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___360_7924.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___360_7924.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7927,FStar_Syntax_Syntax.Tm_type uu____7928)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___360_7944 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___360_7944.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___360_7944.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___360_7944.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___360_7944.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___360_7944.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___360_7944.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___360_7944.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___360_7944.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___360_7944.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7947,FStar_Syntax_Syntax.Tm_uvar uu____7948)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___360_7964 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___360_7964.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___360_7964.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___360_7964.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___360_7964.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___360_7964.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___360_7964.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___360_7964.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___360_7964.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___360_7964.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7967,FStar_Syntax_Syntax.Tm_uvar uu____7968)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7983,uu____7984)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7999,FStar_Syntax_Syntax.Tm_uvar uu____8000)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8015,uu____8016) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7731 with
                     | (rank,tp1) ->
                         let uu____8029 =
                           FStar_All.pipe_right
                             (let uu___361_8033 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___361_8033.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___361_8033.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___361_8033.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___361_8033.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___361_8033.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___361_8033.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___361_8033.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___361_8033.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___361_8033.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____8029))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8039 =
            FStar_All.pipe_right
              (let uu___362_8043 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___362_8043.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___362_8043.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___362_8043.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___362_8043.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___362_8043.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___362_8043.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___362_8043.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___362_8043.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___362_8043.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8039)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8104 probs =
      match uu____8104 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8185 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8206 = rank wl.tcenv hd1  in
               (match uu____8206 with
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
                      (let uu____8265 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8269 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8269)
                          in
                       if uu____8265
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
          let uu____8337 = FStar_Syntax_Util.head_and_args t  in
          match uu____8337 with
          | (hd1,uu____8355) ->
              let uu____8380 =
                let uu____8381 = FStar_Syntax_Subst.compress hd1  in
                uu____8381.FStar_Syntax_Syntax.n  in
              (match uu____8380 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8385) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8419  ->
                           match uu____8419 with
                           | (y,uu____8427) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8449  ->
                                       match uu____8449 with
                                       | (x,uu____8457) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8462 -> false)
           in
        let uu____8463 = rank tcenv p  in
        match uu____8463 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8470 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8497 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8511 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8525 -> false
  
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
                        let uu____8577 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8577 with
                        | (k,uu____8583) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8593 -> false)))
            | uu____8594 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8646 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8652 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8652 = (Prims.parse_int "0")))
                           in
                        if uu____8646 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8668 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8674 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8674 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8668)
               in
            let uu____8675 = filter1 u12  in
            let uu____8678 = filter1 u22  in (uu____8675, uu____8678)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____8708 = filter_out_common_univs us1 us2  in
                   (match uu____8708 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____8767 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____8767 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____8770 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____8780 =
                             let uu____8781 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____8782 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____8781 uu____8782
                              in
                           UFailed uu____8780))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____8806 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____8806 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____8832 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____8832 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____8835 ->
                   let uu____8840 =
                     let uu____8841 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____8842 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____8841
                       uu____8842 msg
                      in
                   UFailed uu____8840)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8843,uu____8844) ->
              let uu____8845 =
                let uu____8846 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8847 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8846 uu____8847
                 in
              failwith uu____8845
          | (FStar_Syntax_Syntax.U_unknown ,uu____8848) ->
              let uu____8849 =
                let uu____8850 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8851 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8850 uu____8851
                 in
              failwith uu____8849
          | (uu____8852,FStar_Syntax_Syntax.U_bvar uu____8853) ->
              let uu____8854 =
                let uu____8855 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8856 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8855 uu____8856
                 in
              failwith uu____8854
          | (uu____8857,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8858 =
                let uu____8859 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8860 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8859 uu____8860
                 in
              failwith uu____8858
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8884 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8884
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8898 = occurs_univ v1 u3  in
              if uu____8898
              then
                let uu____8899 =
                  let uu____8900 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8901 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8900 uu____8901
                   in
                try_umax_components u11 u21 uu____8899
              else
                (let uu____8903 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8903)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8915 = occurs_univ v1 u3  in
              if uu____8915
              then
                let uu____8916 =
                  let uu____8917 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8918 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8917 uu____8918
                   in
                try_umax_components u11 u21 uu____8916
              else
                (let uu____8920 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8920)
          | (FStar_Syntax_Syntax.U_max uu____8921,uu____8922) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8928 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8928
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8930,FStar_Syntax_Syntax.U_max uu____8931) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8937 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8937
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8939,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8940,FStar_Syntax_Syntax.U_name
             uu____8941) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8942) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8943) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8944,FStar_Syntax_Syntax.U_succ
             uu____8945) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8946,FStar_Syntax_Syntax.U_zero
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
      let uu____9046 = bc1  in
      match uu____9046 with
      | (bs1,mk_cod1) ->
          let uu____9090 = bc2  in
          (match uu____9090 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9201 = aux xs ys  in
                     (match uu____9201 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9284 =
                       let uu____9291 = mk_cod1 xs  in ([], uu____9291)  in
                     let uu____9294 =
                       let uu____9301 = mk_cod2 ys  in ([], uu____9301)  in
                     (uu____9284, uu____9294)
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
                  let uu____9369 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9369 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9372 =
                    let uu____9373 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9373 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9372
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9378 = has_type_guard t1 t2  in (uu____9378, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9379 = has_type_guard t2 t1  in (uu____9379, wl)
  
let is_flex_pat :
  'Auu____9388 'Auu____9389 'Auu____9390 .
    ('Auu____9388,'Auu____9389,'Auu____9390 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___339_9403  ->
    match uu___339_9403 with
    | (uu____9412,uu____9413,[]) -> true
    | uu____9416 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9447 = f  in
      match uu____9447 with
      | (uu____9454,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9455;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9456;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9459;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9460;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9461;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9521  ->
                 match uu____9521 with
                 | (y,uu____9529) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9683 =
                  let uu____9698 =
                    let uu____9701 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9701  in
                  ((FStar_List.rev pat_binders), uu____9698)  in
                FStar_Pervasives_Native.Some uu____9683
            | (uu____9734,[]) ->
                let uu____9765 =
                  let uu____9780 =
                    let uu____9783 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9783  in
                  ((FStar_List.rev pat_binders), uu____9780)  in
                FStar_Pervasives_Native.Some uu____9765
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9874 =
                  let uu____9875 = FStar_Syntax_Subst.compress a  in
                  uu____9875.FStar_Syntax_Syntax.n  in
                (match uu____9874 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9895 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9895
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___363_9922 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___363_9922.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___363_9922.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9926 =
                            let uu____9927 =
                              let uu____9934 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9934)  in
                            FStar_Syntax_Syntax.NT uu____9927  in
                          [uu____9926]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___364_9950 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___364_9950.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___364_9950.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9951 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9991 =
                  let uu____10006 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10006  in
                (match uu____9991 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10081 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10114 ->
               let uu____10115 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10115 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10434 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10434
       then
         let uu____10435 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10435
       else ());
      (let uu____10437 = next_prob probs  in
       match uu____10437 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___365_10464 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___365_10464.wl_deferred);
               ctr = (uu___365_10464.ctr);
               defer_ok = (uu___365_10464.defer_ok);
               smt_ok = (uu___365_10464.smt_ok);
               umax_heuristic_ok = (uu___365_10464.umax_heuristic_ok);
               tcenv = (uu___365_10464.tcenv);
               wl_implicits = (uu___365_10464.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10472 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10472
                 then
                   let uu____10473 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10473
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
                           (let uu___366_10478 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___366_10478.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___366_10478.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___366_10478.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___366_10478.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___366_10478.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___366_10478.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___366_10478.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___366_10478.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___366_10478.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10500 ->
                let uu____10509 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10568  ->
                          match uu____10568 with
                          | (c,uu____10576,uu____10577) -> c < probs.ctr))
                   in
                (match uu____10509 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10618 =
                            let uu____10623 =
                              FStar_List.map
                                (fun uu____10638  ->
                                   match uu____10638 with
                                   | (uu____10649,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10623, (probs.wl_implicits))  in
                          Success uu____10618
                      | uu____10652 ->
                          let uu____10661 =
                            let uu___367_10662 = probs  in
                            let uu____10663 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10682  ->
                                      match uu____10682 with
                                      | (uu____10689,uu____10690,y) -> y))
                               in
                            {
                              attempting = uu____10663;
                              wl_deferred = rest;
                              ctr = (uu___367_10662.ctr);
                              defer_ok = (uu___367_10662.defer_ok);
                              smt_ok = (uu___367_10662.smt_ok);
                              umax_heuristic_ok =
                                (uu___367_10662.umax_heuristic_ok);
                              tcenv = (uu___367_10662.tcenv);
                              wl_implicits = (uu___367_10662.wl_implicits)
                            }  in
                          solve env uu____10661))))

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
            let uu____10697 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10697 with
            | USolved wl1 ->
                let uu____10699 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10699
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
                  let uu____10751 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10751 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10754 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10766;
                  FStar_Syntax_Syntax.vars = uu____10767;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10770;
                  FStar_Syntax_Syntax.vars = uu____10771;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10783,uu____10784) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10791,FStar_Syntax_Syntax.Tm_uinst uu____10792) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10799 -> USolved wl

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
            ((let uu____10809 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10809
              then
                let uu____10810 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10810 msg
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
               let uu____10896 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10896 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10949 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10949
                then
                  let uu____10950 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10951 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10950 uu____10951
                else ());
               (let uu____10953 = head_matches_delta env1 wl2 t1 t2  in
                match uu____10953 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10998 = eq_prob t1 t2 wl2  in
                         (match uu____10998 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11019 ->
                         let uu____11028 = eq_prob t1 t2 wl2  in
                         (match uu____11028 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11077 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11092 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11093 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11092, uu____11093)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11098 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11099 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11098, uu____11099)
                            in
                         (match uu____11077 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11130 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11130 with
                                | (t1_hd,t1_args) ->
                                    let uu____11175 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11175 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11239 =
                                              let uu____11246 =
                                                let uu____11257 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11257 :: t1_args  in
                                              let uu____11274 =
                                                let uu____11283 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11283 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11332  ->
                                                   fun uu____11333  ->
                                                     fun uu____11334  ->
                                                       match (uu____11332,
                                                               uu____11333,
                                                               uu____11334)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11384),
                                                          (a2,uu____11386))
                                                           ->
                                                           let uu____11423 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11423
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11246
                                                uu____11274
                                               in
                                            match uu____11239 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___368_11449 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___368_11449.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___368_11449.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___368_11449.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11457 =
                                                  solve env1 wl'  in
                                                (match uu____11457 with
                                                 | Success (uu____11460,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___369_11464
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___369_11464.attempting);
                                                            wl_deferred =
                                                              (uu___369_11464.wl_deferred);
                                                            ctr =
                                                              (uu___369_11464.ctr);
                                                            defer_ok =
                                                              (uu___369_11464.defer_ok);
                                                            smt_ok =
                                                              (uu___369_11464.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___369_11464.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___369_11464.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11465 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11497 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11497 with
                                | (t1_base,p1_opt) ->
                                    let uu____11532 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11532 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11630 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11630
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
                                               let uu____11678 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11678
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
                                               let uu____11708 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11708
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
                                               let uu____11738 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11738
                                           | uu____11741 -> t_base  in
                                         let uu____11758 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11758 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11772 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11772, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11779 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11779 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11814 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11814 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11849 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11849
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
                              let uu____11873 = combine t11 t21 wl2  in
                              (match uu____11873 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11906 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11906
                                     then
                                       let uu____11907 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11907
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11946 ts1 =
               match uu____11946 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12009 = pairwise out t wl2  in
                        (match uu____12009 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12045 =
               let uu____12056 = FStar_List.hd ts  in (uu____12056, [], wl1)
                in
             let uu____12065 = FStar_List.tl ts  in
             aux uu____12045 uu____12065  in
           let uu____12072 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12072 with
           | (this_flex,this_rigid) ->
               let uu____12096 =
                 let uu____12097 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12097.FStar_Syntax_Syntax.n  in
               (match uu____12096 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12122 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12122
                    then
                      let uu____12123 = destruct_flex_t this_flex wl  in
                      (match uu____12123 with
                       | (flex,wl1) ->
                           let uu____12130 = quasi_pattern env flex  in
                           (match uu____12130 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12148 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12148
                                  then
                                    let uu____12149 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12149
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12152 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___370_12155 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___370_12155.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___370_12155.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___370_12155.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___370_12155.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___370_12155.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___370_12155.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___370_12155.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___370_12155.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___370_12155.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12152)
                | uu____12156 ->
                    ((let uu____12158 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12158
                      then
                        let uu____12159 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12159
                      else ());
                     (let uu____12161 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12161 with
                      | (u,_args) ->
                          let uu____12204 =
                            let uu____12205 = FStar_Syntax_Subst.compress u
                               in
                            uu____12205.FStar_Syntax_Syntax.n  in
                          (match uu____12204 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12232 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12232 with
                                 | (u',uu____12250) ->
                                     let uu____12275 =
                                       let uu____12276 = whnf env u'  in
                                       uu____12276.FStar_Syntax_Syntax.n  in
                                     (match uu____12275 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12297 -> false)
                                  in
                               let uu____12298 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___340_12321  ->
                                         match uu___340_12321 with
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
                                              | uu____12330 -> false)
                                         | uu____12333 -> false))
                                  in
                               (match uu____12298 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12347 = whnf env this_rigid
                                         in
                                      let uu____12348 =
                                        FStar_List.collect
                                          (fun uu___341_12354  ->
                                             match uu___341_12354 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12360 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12360]
                                             | uu____12362 -> [])
                                          bounds_probs
                                         in
                                      uu____12347 :: uu____12348  in
                                    let uu____12363 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12363 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12394 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12409 =
                                               let uu____12410 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12410.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12409 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12422 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12422)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12431 -> bound  in
                                           let uu____12432 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12432)  in
                                         (match uu____12394 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12461 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12461
                                                then
                                                  let wl'1 =
                                                    let uu___371_12463 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___371_12463.wl_deferred);
                                                      ctr =
                                                        (uu___371_12463.ctr);
                                                      defer_ok =
                                                        (uu___371_12463.defer_ok);
                                                      smt_ok =
                                                        (uu___371_12463.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___371_12463.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___371_12463.tcenv);
                                                      wl_implicits =
                                                        (uu___371_12463.wl_implicits)
                                                    }  in
                                                  let uu____12464 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12464
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12467 =
                                                  solve_t env eq_prob
                                                    (let uu___372_12469 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___372_12469.wl_deferred);
                                                       ctr =
                                                         (uu___372_12469.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___372_12469.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___372_12469.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___372_12469.tcenv);
                                                       wl_implicits =
                                                         (uu___372_12469.wl_implicits)
                                                     })
                                                   in
                                                match uu____12467 with
                                                | Success uu____12470 ->
                                                    let wl2 =
                                                      let uu___373_12476 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___373_12476.wl_deferred);
                                                        ctr =
                                                          (uu___373_12476.ctr);
                                                        defer_ok =
                                                          (uu___373_12476.defer_ok);
                                                        smt_ok =
                                                          (uu___373_12476.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___373_12476.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___373_12476.tcenv);
                                                        wl_implicits =
                                                          (uu___373_12476.wl_implicits)
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
                                                    let uu____12491 =
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
                                                    ((let uu____12502 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12502
                                                      then
                                                        let uu____12503 =
                                                          let uu____12504 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12504
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12503
                                                      else ());
                                                     (let uu____12510 =
                                                        let uu____12525 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12525)
                                                         in
                                                      match uu____12510 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12547))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12573 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12573
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
                                                                  let uu____12590
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12590))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12615 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12615
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
                                                                    let uu____12633
                                                                    =
                                                                    let uu____12638
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12638
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12633
                                                                    [] wl2
                                                                     in
                                                                  let uu____12643
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12643))))
                                                      | uu____12644 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12659 when flip ->
                               let uu____12660 =
                                 let uu____12661 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12662 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12661 uu____12662
                                  in
                               failwith uu____12660
                           | uu____12663 ->
                               let uu____12664 =
                                 let uu____12665 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12666 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12665 uu____12666
                                  in
                               failwith uu____12664)))))

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
                      (fun uu____12700  ->
                         match uu____12700 with
                         | (x,i) ->
                             let uu____12719 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12719, i)) bs_lhs
                     in
                  let uu____12722 = lhs  in
                  match uu____12722 with
                  | (uu____12723,u_lhs,uu____12725) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12822 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12832 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12832, univ)
                             in
                          match uu____12822 with
                          | (k,univ) ->
                              let uu____12839 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12839 with
                               | (uu____12856,u,wl3) ->
                                   let uu____12859 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12859, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12885 =
                              let uu____12898 =
                                let uu____12909 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12909 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12960  ->
                                   fun uu____12961  ->
                                     match (uu____12960, uu____12961) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13062 =
                                           let uu____13069 =
                                             let uu____13072 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13072
                                              in
                                           copy_uvar u_lhs [] uu____13069 wl2
                                            in
                                         (match uu____13062 with
                                          | (uu____13101,t_a,wl3) ->
                                              let uu____13104 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13104 with
                                               | (uu____13123,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12898
                                ([], wl1)
                               in
                            (match uu____12885 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___374_13179 = ct  in
                                   let uu____13180 =
                                     let uu____13183 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13183
                                      in
                                   let uu____13198 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___374_13179.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___374_13179.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13180;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13198;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___374_13179.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___375_13216 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___375_13216.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___375_13216.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13219 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13219 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13281 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13281 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13292 =
                                          let uu____13297 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13297)  in
                                        TERM uu____13292  in
                                      let uu____13298 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13298 with
                                       | (sub_prob,wl3) ->
                                           let uu____13311 =
                                             let uu____13312 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13312
                                              in
                                           solve env uu____13311))
                             | (x,imp)::formals2 ->
                                 let uu____13334 =
                                   let uu____13341 =
                                     let uu____13344 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13344
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13341 wl1
                                    in
                                 (match uu____13334 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13365 =
                                          let uu____13368 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13368
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13365 u_x
                                         in
                                      let uu____13369 =
                                        let uu____13372 =
                                          let uu____13375 =
                                            let uu____13376 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13376, imp)  in
                                          [uu____13375]  in
                                        FStar_List.append bs_terms
                                          uu____13372
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13369 formals2 wl2)
                              in
                           let uu____13403 = occurs_check u_lhs arrow1  in
                           (match uu____13403 with
                            | (uu____13414,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13425 =
                                    let uu____13426 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13426
                                     in
                                  giveup_or_defer env orig wl uu____13425
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
              (let uu____13455 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13455
               then
                 let uu____13456 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13457 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13456 (rel_to_string (p_rel orig)) uu____13457
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13578 = rhs wl1 scope env1 subst1  in
                     (match uu____13578 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13598 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13598
                            then
                              let uu____13599 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13599
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____13672 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____13672 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___376_13674 = hd1  in
                       let uu____13675 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___376_13674.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___376_13674.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13675
                       }  in
                     let hd21 =
                       let uu___377_13679 = hd2  in
                       let uu____13680 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___377_13679.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___377_13679.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13680
                       }  in
                     let uu____13683 =
                       let uu____13688 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13688
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13683 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13707 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13707
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13711 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13711 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13774 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13774
                                  in
                               ((let uu____13792 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13792
                                 then
                                   let uu____13793 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13794 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13793
                                     uu____13794
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13821 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13854 = aux wl [] env [] bs1 bs2  in
               match uu____13854 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13903 = attempt sub_probs wl2  in
                   solve env uu____13903)

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
            let uu___378_13923 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___378_13923.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___378_13923.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____13931 = try_solve env wl'  in
          match uu____13931 with
          | Success (uu____13932,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___379_13936 = wl  in
                  {
                    attempting = (uu___379_13936.attempting);
                    wl_deferred = (uu___379_13936.wl_deferred);
                    ctr = (uu___379_13936.ctr);
                    defer_ok = (uu___379_13936.defer_ok);
                    smt_ok = (uu___379_13936.smt_ok);
                    umax_heuristic_ok = (uu___379_13936.umax_heuristic_ok);
                    tcenv = (uu___379_13936.tcenv);
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
        (let uu____13944 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13944 wl)

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
              let uu____13958 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13958 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13992 = lhs1  in
              match uu____13992 with
              | (uu____13995,ctx_u,uu____13997) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____14005 ->
                        let uu____14006 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____14006 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____14053 = quasi_pattern env1 lhs1  in
              match uu____14053 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____14083) ->
                  let uu____14088 = lhs1  in
                  (match uu____14088 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____14102 = occurs_check ctx_u rhs1  in
                       (match uu____14102 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14144 =
                                let uu____14151 =
                                  let uu____14152 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14152
                                   in
                                FStar_Util.Inl uu____14151  in
                              (uu____14144, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14174 =
                                 let uu____14175 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14175  in
                               if uu____14174
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14195 =
                                    let uu____14202 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14202  in
                                  let uu____14207 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14195, uu____14207)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____14250 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14250 with
              | (rhs_hd,args) ->
                  let uu____14293 = FStar_Util.prefix args  in
                  (match uu____14293 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14365 = lhs1  in
                       (match uu____14365 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14369 =
                              let uu____14380 =
                                let uu____14387 =
                                  let uu____14390 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14390
                                   in
                                copy_uvar u_lhs [] uu____14387 wl1  in
                              match uu____14380 with
                              | (uu____14417,t_last_arg,wl2) ->
                                  let uu____14420 =
                                    let uu____14427 =
                                      let uu____14428 =
                                        let uu____14437 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14437]  in
                                      FStar_List.append bs_lhs uu____14428
                                       in
                                    copy_uvar u_lhs uu____14427 t_res_lhs wl2
                                     in
                                  (match uu____14420 with
                                   | (uu____14472,lhs',wl3) ->
                                       let uu____14475 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14475 with
                                        | (uu____14492,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14369 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14513 =
                                     let uu____14514 =
                                       let uu____14519 =
                                         let uu____14520 =
                                           let uu____14523 =
                                             let uu____14528 =
                                               let uu____14529 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14529]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14528
                                              in
                                           uu____14523
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14520
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14519)  in
                                     TERM uu____14514  in
                                   [uu____14513]  in
                                 let uu____14556 =
                                   let uu____14563 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14563 with
                                   | (p1,wl3) ->
                                       let uu____14582 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14582 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14556 with
                                  | (sub_probs,wl3) ->
                                      let uu____14613 =
                                        let uu____14614 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14614  in
                                      solve env1 uu____14613))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14647 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14647 with
                | (uu____14664,args) ->
                    (match args with | [] -> false | uu____14698 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14715 =
                  let uu____14716 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14716.FStar_Syntax_Syntax.n  in
                match uu____14715 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14719 -> true
                | uu____14734 -> false  in
              let uu____14735 = quasi_pattern env1 lhs1  in
              match uu____14735 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14746 =
                    let uu____14747 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14747
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14746
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14754 = is_app rhs1  in
                  if uu____14754
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14756 = is_arrow rhs1  in
                     if uu____14756
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14758 =
                          let uu____14759 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14759
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14758))
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
                let uu____14762 = lhs  in
                (match uu____14762 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14766 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14766 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14783 =
                              let uu____14786 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14786
                               in
                            FStar_All.pipe_right uu____14783
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14803 = occurs_check ctx_uv rhs1  in
                          (match uu____14803 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14825 =
                                   let uu____14826 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14826
                                    in
                                 giveup_or_defer env orig wl uu____14825
                               else
                                 (let uu____14828 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14828
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14833 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14833
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14835 =
                                         let uu____14836 =
                                           names_to_string1 fvs2  in
                                         let uu____14837 =
                                           names_to_string1 fvs1  in
                                         let uu____14838 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14836 uu____14837
                                           uu____14838
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14835)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14846 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14850 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14850 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14873 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14873
                             | (FStar_Util.Inl msg,uu____14875) ->
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
                  (let uu____14908 =
                     let uu____14925 = quasi_pattern env lhs  in
                     let uu____14932 = quasi_pattern env rhs  in
                     (uu____14925, uu____14932)  in
                   match uu____14908 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14975 = lhs  in
                       (match uu____14975 with
                        | ({ FStar_Syntax_Syntax.n = uu____14976;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14978;_},u_lhs,uu____14980)
                            ->
                            let uu____14983 = rhs  in
                            (match uu____14983 with
                             | (uu____14984,u_rhs,uu____14986) ->
                                 let uu____14987 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14987
                                 then
                                   let uu____14992 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14992
                                 else
                                   (let uu____14994 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____14994 with
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
                                        let uu____15026 =
                                          let uu____15033 =
                                            let uu____15036 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____15036
                                             in
                                          new_uvar
                                            (Prims.strcat "flex-flex quasi:"
                                               (Prims.strcat "\tlhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____15033
                                            FStar_Syntax_Syntax.Strict
                                           in
                                        (match uu____15026 with
                                         | (uu____15039,w,wl1) ->
                                             let w_app =
                                               let uu____15045 =
                                                 let uu____15050 =
                                                   FStar_List.map
                                                     (fun uu____15061  ->
                                                        match uu____15061
                                                        with
                                                        | (z,uu____15069) ->
                                                            let uu____15074 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15074) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15050
                                                  in
                                               uu____15045
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____15078 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____15078
                                               then
                                                 let uu____15079 =
                                                   let uu____15082 =
                                                     flex_t_to_string lhs  in
                                                   let uu____15083 =
                                                     let uu____15086 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____15087 =
                                                       let uu____15090 =
                                                         term_to_string w  in
                                                       let uu____15091 =
                                                         let uu____15094 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____15101 =
                                                           let uu____15104 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____15111 =
                                                             let uu____15114
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____15114]
                                                              in
                                                           uu____15104 ::
                                                             uu____15111
                                                            in
                                                         uu____15094 ::
                                                           uu____15101
                                                          in
                                                       uu____15090 ::
                                                         uu____15091
                                                        in
                                                     uu____15086 ::
                                                       uu____15087
                                                      in
                                                   uu____15082 :: uu____15083
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____15079
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____15120 =
                                                     let uu____15125 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____15125)  in
                                                   TERM uu____15120  in
                                                 let uu____15126 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____15126
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____15131 =
                                                        let uu____15136 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____15136)
                                                         in
                                                      TERM uu____15131  in
                                                    [s1; s2])
                                                  in
                                               let uu____15137 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____15137))))))
                   | uu____15138 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____15203 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15203
            then
              let uu____15204 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15205 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15206 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15207 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15204 uu____15205 uu____15206 uu____15207
            else ());
           (let uu____15210 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15210 with
            | (head1,args1) ->
                let uu____15253 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15253 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____15318 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____15318 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15343 =
                         let uu____15344 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15345 = args_to_string args1  in
                         let uu____15348 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15349 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15344 uu____15345 uu____15348 uu____15349
                          in
                       giveup env1 uu____15343 orig
                     else
                       (let uu____15353 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15359 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15359 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15353
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___380_15361 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___380_15361.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___380_15361.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___380_15361.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___380_15361.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___380_15361.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___380_15361.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___380_15361.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___380_15361.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____15368 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____15368
                                    else solve env1 wl2))
                        else
                          (let uu____15371 = base_and_refinement env1 t1  in
                           match uu____15371 with
                           | (base1,refinement1) ->
                               let uu____15396 = base_and_refinement env1 t2
                                  in
                               (match uu____15396 with
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
                                           let uu____15559 =
                                             FStar_List.fold_right
                                               (fun uu____15599  ->
                                                  fun uu____15600  ->
                                                    match (uu____15599,
                                                            uu____15600)
                                                    with
                                                    | (((a1,uu____15652),
                                                        (a2,uu____15654)),
                                                       (probs,wl3)) ->
                                                        let uu____15703 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15703
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____15559 with
                                           | (subprobs,wl3) ->
                                               ((let uu____15745 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____15745
                                                 then
                                                   let uu____15746 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____15746
                                                 else ());
                                                (let uu____15749 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____15749
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
                                                    (let uu____15769 =
                                                       mk_sub_probs wl3  in
                                                     match uu____15769 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____15785 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____15785
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____15793 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____15793))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____15816 =
                                                    mk_sub_probs wl3  in
                                                  match uu____15816 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____15830 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____15830)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____15855 =
                                           match uu____15855 with
                                           | (prob,reason) ->
                                               ((let uu____15863 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____15863
                                                 then
                                                   let uu____15864 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____15865 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____15864 uu____15865
                                                     reason
                                                 else ());
                                                (let uu____15867 =
                                                   let uu____15876 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____15879 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____15876, uu____15879)
                                                    in
                                                 match uu____15867 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____15892 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____15892 with
                                                      | (head1',uu____15910)
                                                          ->
                                                          let uu____15935 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____15935
                                                           with
                                                           | (head2',uu____15953)
                                                               ->
                                                               let uu____15978
                                                                 =
                                                                 let uu____15983
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____15984
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____15983,
                                                                   uu____15984)
                                                                  in
                                                               (match uu____15978
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____15986
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____15986
                                                                    then
                                                                    let uu____15987
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____15988
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____15989
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____15990
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____15987
                                                                    uu____15988
                                                                    uu____15989
                                                                    uu____15990
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____15992
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___381_16000
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___381_16000.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____16002
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____16002
                                                                    then
                                                                    let uu____16003
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16003
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16005 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____16017 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____16017 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____16024 =
                                             let uu____16025 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____16025.FStar_Syntax_Syntax.n
                                              in
                                           match uu____16024 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16029 -> false  in
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
                                          | uu____16031 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16034 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___382_16070 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___382_16070.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___382_16070.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___382_16070.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___382_16070.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___382_16070.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___382_16070.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___382_16070.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___382_16070.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16145 = destruct_flex_t scrutinee wl1  in
             match uu____16145 with
             | ((_t,uv,_args),wl2) ->
                 let uu____16156 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____16156 with
                  | (xs,pat_term,uu____16171,uu____16172) ->
                      let uu____16177 =
                        FStar_List.fold_left
                          (fun uu____16200  ->
                             fun x  ->
                               match uu____16200 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____16221 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____16221 with
                                    | (uu____16240,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____16177 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____16261 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____16261 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___383_16277 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___383_16277.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___383_16277.umax_heuristic_ok);
                                    tcenv = (uu___383_16277.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____16285 = solve env1 wl'  in
                                (match uu____16285 with
                                 | Success (uu____16288,imps) ->
                                     let wl'1 =
                                       let uu___384_16291 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___384_16291.wl_deferred);
                                         ctr = (uu___384_16291.ctr);
                                         defer_ok = (uu___384_16291.defer_ok);
                                         smt_ok = (uu___384_16291.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___384_16291.umax_heuristic_ok);
                                         tcenv = (uu___384_16291.tcenv);
                                         wl_implicits =
                                           (uu___384_16291.wl_implicits)
                                       }  in
                                     let uu____16292 = solve env1 wl'1  in
                                     (match uu____16292 with
                                      | Success (uu____16295,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___385_16299 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___385_16299.attempting);
                                                 wl_deferred =
                                                   (uu___385_16299.wl_deferred);
                                                 ctr = (uu___385_16299.ctr);
                                                 defer_ok =
                                                   (uu___385_16299.defer_ok);
                                                 smt_ok =
                                                   (uu___385_16299.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___385_16299.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___385_16299.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16300 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16306 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16327 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16327
                 then
                   let uu____16328 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16329 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16328 uu____16329
                 else ());
                (let uu____16331 =
                   let uu____16352 =
                     let uu____16361 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16361)  in
                   let uu____16368 =
                     let uu____16377 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16377)  in
                   (uu____16352, uu____16368)  in
                 match uu____16331 with
                 | ((uu____16406,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16409;
                                   FStar_Syntax_Syntax.vars = uu____16410;_}),
                    (s,t)) ->
                     let uu____16481 =
                       let uu____16482 = is_flex scrutinee  in
                       Prims.op_Negation uu____16482  in
                     if uu____16481
                     then
                       ((let uu____16490 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16490
                         then
                           let uu____16491 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16491
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16503 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16503
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16509 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16509
                           then
                             let uu____16510 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16511 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16510 uu____16511
                           else ());
                          (let pat_discriminates uu___342_16532 =
                             match uu___342_16532 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16547;
                                  FStar_Syntax_Syntax.p = uu____16548;_},FStar_Pervasives_Native.None
                                ,uu____16549) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16562;
                                  FStar_Syntax_Syntax.p = uu____16563;_},FStar_Pervasives_Native.None
                                ,uu____16564) -> true
                             | uu____16589 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16689 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16689 with
                                       | (uu____16690,uu____16691,t') ->
                                           let uu____16709 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____16709 with
                                            | (FullMatch ,uu____16720) ->
                                                true
                                            | (HeadMatch
                                               uu____16733,uu____16734) ->
                                                true
                                            | uu____16747 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16780 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16780
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16785 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16785 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16873,uu____16874) ->
                                       branches1
                                   | uu____17019 -> branches  in
                                 let uu____17074 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17083 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17083 with
                                        | (p,uu____17087,uu____17088) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____17074))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17144 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17144 with
                                | (p,uu____17152,e) ->
                                    ((let uu____17171 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17171
                                      then
                                        let uu____17172 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17173 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17172 uu____17173
                                      else ());
                                     (let uu____17175 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____17175)))))
                 | ((s,t),(uu____17190,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____17193;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17194;_}))
                     ->
                     let uu____17263 =
                       let uu____17264 = is_flex scrutinee  in
                       Prims.op_Negation uu____17264  in
                     if uu____17263
                     then
                       ((let uu____17272 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____17272
                         then
                           let uu____17273 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17273
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17285 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17285
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17291 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17291
                           then
                             let uu____17292 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____17293 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17292 uu____17293
                           else ());
                          (let pat_discriminates uu___342_17314 =
                             match uu___342_17314 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17329;
                                  FStar_Syntax_Syntax.p = uu____17330;_},FStar_Pervasives_Native.None
                                ,uu____17331) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17344;
                                  FStar_Syntax_Syntax.p = uu____17345;_},FStar_Pervasives_Native.None
                                ,uu____17346) -> true
                             | uu____17371 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17471 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17471 with
                                       | (uu____17472,uu____17473,t') ->
                                           let uu____17491 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____17491 with
                                            | (FullMatch ,uu____17502) ->
                                                true
                                            | (HeadMatch
                                               uu____17515,uu____17516) ->
                                                true
                                            | uu____17529 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17562 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17562
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17567 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17567 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17655,uu____17656) ->
                                       branches1
                                   | uu____17801 -> branches  in
                                 let uu____17856 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17865 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17865 with
                                        | (p,uu____17869,uu____17870) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17856))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17926 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17926 with
                                | (p,uu____17934,e) ->
                                    ((let uu____17953 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17953
                                      then
                                        let uu____17954 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17955 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17954 uu____17955
                                      else ());
                                     (let uu____17957 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17957)))))
                 | uu____17970 ->
                     ((let uu____17992 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17992
                       then
                         let uu____17993 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17994 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17993 uu____17994
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____18036 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____18036
            then
              let uu____18037 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____18038 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____18039 = FStar_Syntax_Print.term_to_string t1  in
              let uu____18040 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18037 uu____18038 uu____18039 uu____18040
            else ());
           (let uu____18042 = head_matches_delta env1 wl1 t1 t2  in
            match uu____18042 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____18073,uu____18074) ->
                     let rec may_relate head3 =
                       let uu____18101 =
                         let uu____18102 = FStar_Syntax_Subst.compress head3
                            in
                         uu____18102.FStar_Syntax_Syntax.n  in
                       match uu____18101 with
                       | FStar_Syntax_Syntax.Tm_name uu____18105 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18106 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____18130 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____18130 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____18131 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____18132
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____18133 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____18135,uu____18136) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____18178) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____18184) ->
                           may_relate t
                       | uu____18189 -> false  in
                     let uu____18190 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____18190 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____18205 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____18205
                          then
                            let uu____18206 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____18206 with
                             | (guard,wl2) ->
                                 let uu____18213 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____18213)
                          else
                            (let uu____18215 =
                               let uu____18216 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____18217 =
                                 let uu____18218 =
                                   let uu____18221 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____18221
                                     (fun x  ->
                                        let uu____18227 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____18227)
                                    in
                                 FStar_Util.dflt "" uu____18218  in
                               let uu____18228 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____18229 =
                                 let uu____18230 =
                                   let uu____18233 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____18233
                                     (fun x  ->
                                        let uu____18239 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____18239)
                                    in
                                 FStar_Util.dflt "" uu____18230  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____18216 uu____18217 uu____18228
                                 uu____18229
                                in
                             giveup env1 uu____18215 orig))
                 | (HeadMatch (true ),uu____18240) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18253 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____18253 with
                        | (guard,wl2) ->
                            let uu____18260 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____18260)
                     else
                       (let uu____18262 =
                          let uu____18263 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____18264 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____18263 uu____18264
                           in
                        giveup env1 uu____18262 orig)
                 | (uu____18265,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___386_18279 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___386_18279.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___386_18279.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___386_18279.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___386_18279.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___386_18279.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___386_18279.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___386_18279.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___386_18279.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18303 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18303
          then
            let uu____18304 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18304
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18309 =
                let uu____18312 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18312  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18309 t1);
             (let uu____18330 =
                let uu____18333 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18333  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18330 t2);
             (let uu____18351 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18351
              then
                let uu____18352 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18353 =
                  let uu____18354 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18355 =
                    let uu____18356 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18356  in
                  Prims.strcat uu____18354 uu____18355  in
                let uu____18357 =
                  let uu____18358 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18359 =
                    let uu____18360 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18360  in
                  Prims.strcat uu____18358 uu____18359  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18352
                  uu____18353 uu____18357
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18363,uu____18364) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18387,FStar_Syntax_Syntax.Tm_delayed uu____18388) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18411,uu____18412) ->
                  let uu____18439 =
                    let uu___387_18440 = problem  in
                    let uu____18441 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___387_18440.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18441;
                      FStar_TypeChecker_Common.relation =
                        (uu___387_18440.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___387_18440.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___387_18440.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___387_18440.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___387_18440.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___387_18440.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___387_18440.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___387_18440.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18439 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18442,uu____18443) ->
                  let uu____18450 =
                    let uu___388_18451 = problem  in
                    let uu____18452 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___388_18451.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18452;
                      FStar_TypeChecker_Common.relation =
                        (uu___388_18451.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___388_18451.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___388_18451.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___388_18451.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___388_18451.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___388_18451.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___388_18451.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___388_18451.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18450 wl
              | (uu____18453,FStar_Syntax_Syntax.Tm_ascribed uu____18454) ->
                  let uu____18481 =
                    let uu___389_18482 = problem  in
                    let uu____18483 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___389_18482.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___389_18482.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___389_18482.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18483;
                      FStar_TypeChecker_Common.element =
                        (uu___389_18482.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___389_18482.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___389_18482.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___389_18482.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___389_18482.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___389_18482.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18481 wl
              | (uu____18484,FStar_Syntax_Syntax.Tm_meta uu____18485) ->
                  let uu____18492 =
                    let uu___390_18493 = problem  in
                    let uu____18494 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___390_18493.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___390_18493.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___390_18493.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18494;
                      FStar_TypeChecker_Common.element =
                        (uu___390_18493.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___390_18493.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___390_18493.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___390_18493.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___390_18493.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___390_18493.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18492 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18496),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18498)) ->
                  let uu____18507 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18507
              | (FStar_Syntax_Syntax.Tm_bvar uu____18508,uu____18509) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18510,FStar_Syntax_Syntax.Tm_bvar uu____18511) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___343_18580 =
                    match uu___343_18580 with
                    | [] -> c
                    | bs ->
                        let uu____18608 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18608
                     in
                  let uu____18619 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18619 with
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
                                    let uu____18768 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18768
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
                  let mk_t t l uu___344_18853 =
                    match uu___344_18853 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18895 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18895 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____19040 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____19041 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____19040
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____19041 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____19042,uu____19043) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19072 -> true
                    | uu____19091 -> false  in
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
                      (let uu____19144 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___391_19152 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___391_19152.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___391_19152.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___391_19152.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___391_19152.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___391_19152.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___391_19152.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___391_19152.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___391_19152.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___391_19152.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___391_19152.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___391_19152.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___391_19152.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___391_19152.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___391_19152.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___391_19152.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___391_19152.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___391_19152.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___391_19152.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___391_19152.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___391_19152.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___391_19152.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___391_19152.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___391_19152.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___391_19152.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___391_19152.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___391_19152.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___391_19152.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___391_19152.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___391_19152.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___391_19152.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___391_19152.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___391_19152.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___391_19152.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___391_19152.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___391_19152.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___391_19152.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___391_19152.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___391_19152.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___391_19152.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___391_19152.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19144 with
                       | (uu____19155,ty,uu____19157) ->
                           let uu____19158 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19158)
                     in
                  let uu____19159 =
                    let uu____19176 = maybe_eta t1  in
                    let uu____19183 = maybe_eta t2  in
                    (uu____19176, uu____19183)  in
                  (match uu____19159 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___392_19225 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___392_19225.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___392_19225.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___392_19225.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___392_19225.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___392_19225.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___392_19225.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___392_19225.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___392_19225.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19246 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19246
                       then
                         let uu____19247 = destruct_flex_t not_abs wl  in
                         (match uu____19247 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19262 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19262.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19262.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19262.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19262.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19262.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19262.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19262.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19262.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19284 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19284
                       then
                         let uu____19285 = destruct_flex_t not_abs wl  in
                         (match uu____19285 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19300 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19300.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19300.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19300.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19300.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19300.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19300.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19300.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19300.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19302 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19319,FStar_Syntax_Syntax.Tm_abs uu____19320) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19349 -> true
                    | uu____19368 -> false  in
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
                      (let uu____19421 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___391_19429 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___391_19429.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___391_19429.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___391_19429.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___391_19429.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___391_19429.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___391_19429.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___391_19429.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___391_19429.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___391_19429.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___391_19429.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___391_19429.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___391_19429.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___391_19429.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___391_19429.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___391_19429.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___391_19429.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___391_19429.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___391_19429.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___391_19429.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___391_19429.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___391_19429.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___391_19429.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___391_19429.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___391_19429.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___391_19429.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___391_19429.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___391_19429.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___391_19429.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___391_19429.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___391_19429.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___391_19429.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___391_19429.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___391_19429.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___391_19429.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___391_19429.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___391_19429.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___391_19429.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___391_19429.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___391_19429.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___391_19429.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19421 with
                       | (uu____19432,ty,uu____19434) ->
                           let uu____19435 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19435)
                     in
                  let uu____19436 =
                    let uu____19453 = maybe_eta t1  in
                    let uu____19460 = maybe_eta t2  in
                    (uu____19453, uu____19460)  in
                  (match uu____19436 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___392_19502 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___392_19502.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___392_19502.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___392_19502.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___392_19502.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___392_19502.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___392_19502.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___392_19502.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___392_19502.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19523 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19523
                       then
                         let uu____19524 = destruct_flex_t not_abs wl  in
                         (match uu____19524 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19539 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19539.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19539.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19539.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19539.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19539.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19539.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19539.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19539.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19561 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19561
                       then
                         let uu____19562 = destruct_flex_t not_abs wl  in
                         (match uu____19562 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19577 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19577.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19577.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19577.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19577.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19577.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19577.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19577.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19577.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19579 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19608 =
                    let uu____19613 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19613 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___394_19641 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___394_19641.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___394_19641.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___395_19643 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___395_19643.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___395_19643.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19644,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___394_19658 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___394_19658.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___394_19658.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___395_19660 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___395_19660.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___395_19660.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19661 -> (x1, x2)  in
                  (match uu____19608 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19680 = as_refinement false env t11  in
                       (match uu____19680 with
                        | (x12,phi11) ->
                            let uu____19687 = as_refinement false env t21  in
                            (match uu____19687 with
                             | (x22,phi21) ->
                                 ((let uu____19695 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19695
                                   then
                                     ((let uu____19697 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19698 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19699 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19697
                                         uu____19698 uu____19699);
                                      (let uu____19700 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19701 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19702 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19700
                                         uu____19701 uu____19702))
                                   else ());
                                  (let uu____19704 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19704 with
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
                                         let uu____19772 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19772
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19784 =
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
                                         (let uu____19795 =
                                            let uu____19798 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19798
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19795
                                            (p_guard base_prob));
                                         (let uu____19816 =
                                            let uu____19819 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19819
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19816
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19837 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19837)
                                          in
                                       let has_uvars =
                                         (let uu____19841 =
                                            let uu____19842 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19842
                                             in
                                          Prims.op_Negation uu____19841) ||
                                           (let uu____19846 =
                                              let uu____19847 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19847
                                               in
                                            Prims.op_Negation uu____19846)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19850 =
                                           let uu____19855 =
                                             let uu____19864 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19864]  in
                                           mk_t_problem wl1 uu____19855 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19850 with
                                          | (ref_prob,wl2) ->
                                              let uu____19885 =
                                                solve env1
                                                  (let uu___396_19887 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___396_19887.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___396_19887.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___396_19887.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___396_19887.tcenv);
                                                     wl_implicits =
                                                       (uu___396_19887.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19885 with
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
                                               | Success uu____19897 ->
                                                   let guard =
                                                     let uu____19905 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19905
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___397_19914 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___397_19914.attempting);
                                                       wl_deferred =
                                                         (uu___397_19914.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___397_19914.defer_ok);
                                                       smt_ok =
                                                         (uu___397_19914.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___397_19914.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___397_19914.tcenv);
                                                       wl_implicits =
                                                         (uu___397_19914.wl_implicits)
                                                     }  in
                                                   let uu____19915 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19915))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19917,FStar_Syntax_Syntax.Tm_uvar uu____19918) ->
                  let uu____19943 = destruct_flex_t t1 wl  in
                  (match uu____19943 with
                   | (f1,wl1) ->
                       let uu____19950 = destruct_flex_t t2 wl1  in
                       (match uu____19950 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19957;
                    FStar_Syntax_Syntax.pos = uu____19958;
                    FStar_Syntax_Syntax.vars = uu____19959;_},uu____19960),FStar_Syntax_Syntax.Tm_uvar
                 uu____19961) ->
                  let uu____20010 = destruct_flex_t t1 wl  in
                  (match uu____20010 with
                   | (f1,wl1) ->
                       let uu____20017 = destruct_flex_t t2 wl1  in
                       (match uu____20017 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20024,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20025;
                    FStar_Syntax_Syntax.pos = uu____20026;
                    FStar_Syntax_Syntax.vars = uu____20027;_},uu____20028))
                  ->
                  let uu____20077 = destruct_flex_t t1 wl  in
                  (match uu____20077 with
                   | (f1,wl1) ->
                       let uu____20084 = destruct_flex_t t2 wl1  in
                       (match uu____20084 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20091;
                    FStar_Syntax_Syntax.pos = uu____20092;
                    FStar_Syntax_Syntax.vars = uu____20093;_},uu____20094),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20095;
                    FStar_Syntax_Syntax.pos = uu____20096;
                    FStar_Syntax_Syntax.vars = uu____20097;_},uu____20098))
                  ->
                  let uu____20171 = destruct_flex_t t1 wl  in
                  (match uu____20171 with
                   | (f1,wl1) ->
                       let uu____20178 = destruct_flex_t t2 wl1  in
                       (match uu____20178 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20185,uu____20186) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20199 = destruct_flex_t t1 wl  in
                  (match uu____20199 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20206;
                    FStar_Syntax_Syntax.pos = uu____20207;
                    FStar_Syntax_Syntax.vars = uu____20208;_},uu____20209),uu____20210)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20247 = destruct_flex_t t1 wl  in
                  (match uu____20247 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____20254,FStar_Syntax_Syntax.Tm_uvar uu____20255) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____20268,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20269;
                    FStar_Syntax_Syntax.pos = uu____20270;
                    FStar_Syntax_Syntax.vars = uu____20271;_},uu____20272))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20309,FStar_Syntax_Syntax.Tm_arrow uu____20310) ->
                  solve_t' env
                    (let uu___398_20338 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___398_20338.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___398_20338.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___398_20338.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___398_20338.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___398_20338.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___398_20338.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___398_20338.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___398_20338.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___398_20338.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20339;
                    FStar_Syntax_Syntax.pos = uu____20340;
                    FStar_Syntax_Syntax.vars = uu____20341;_},uu____20342),FStar_Syntax_Syntax.Tm_arrow
                 uu____20343) ->
                  solve_t' env
                    (let uu___398_20395 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___398_20395.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___398_20395.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___398_20395.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___398_20395.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___398_20395.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___398_20395.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___398_20395.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___398_20395.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___398_20395.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20396,FStar_Syntax_Syntax.Tm_uvar uu____20397) ->
                  let uu____20410 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20410
              | (uu____20411,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20412;
                    FStar_Syntax_Syntax.pos = uu____20413;
                    FStar_Syntax_Syntax.vars = uu____20414;_},uu____20415))
                  ->
                  let uu____20452 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20452
              | (FStar_Syntax_Syntax.Tm_uvar uu____20453,uu____20454) ->
                  let uu____20467 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20467
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20468;
                    FStar_Syntax_Syntax.pos = uu____20469;
                    FStar_Syntax_Syntax.vars = uu____20470;_},uu____20471),uu____20472)
                  ->
                  let uu____20509 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20509
              | (FStar_Syntax_Syntax.Tm_refine uu____20510,uu____20511) ->
                  let t21 =
                    let uu____20519 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20519  in
                  solve_t env
                    (let uu___399_20545 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___399_20545.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___399_20545.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___399_20545.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___399_20545.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___399_20545.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___399_20545.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___399_20545.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___399_20545.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___399_20545.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20546,FStar_Syntax_Syntax.Tm_refine uu____20547) ->
                  let t11 =
                    let uu____20555 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20555  in
                  solve_t env
                    (let uu___400_20581 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___400_20581.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___400_20581.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___400_20581.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___400_20581.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___400_20581.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___400_20581.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___400_20581.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___400_20581.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___400_20581.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20663 =
                    let uu____20664 = guard_of_prob env wl problem t1 t2  in
                    match uu____20664 with
                    | (guard,wl1) ->
                        let uu____20671 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20671
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20890 = br1  in
                        (match uu____20890 with
                         | (p1,w1,uu____20919) ->
                             let uu____20936 = br2  in
                             (match uu____20936 with
                              | (p2,w2,uu____20959) ->
                                  let uu____20964 =
                                    let uu____20965 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20965  in
                                  if uu____20964
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20989 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20989 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____21026 = br2  in
                                         (match uu____21026 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____21059 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____21059
                                                 in
                                              let uu____21064 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____21095,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____21116) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____21175 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____21175 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____21064
                                                (fun uu____21246  ->
                                                   match uu____21246 with
                                                   | (wprobs,wl2) ->
                                                       let uu____21283 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____21283
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____21303
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____21303
                                                              then
                                                                let uu____21304
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____21305
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____21304
                                                                  uu____21305
                                                              else ());
                                                             (let uu____21307
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____21307
                                                                (fun
                                                                   uu____21343
                                                                    ->
                                                                   match uu____21343
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
                    | uu____21472 -> FStar_Pervasives_Native.None  in
                  let uu____21513 = solve_branches wl brs1 brs2  in
                  (match uu____21513 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21561 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21561 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____21594 =
                                FStar_List.map
                                  (fun uu____21606  ->
                                     match uu____21606 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21594  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21615 =
                              let uu____21616 =
                                let uu____21617 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____21617
                                  (let uu___401_21625 = wl3  in
                                   {
                                     attempting = (uu___401_21625.attempting);
                                     wl_deferred =
                                       (uu___401_21625.wl_deferred);
                                     ctr = (uu___401_21625.ctr);
                                     defer_ok = (uu___401_21625.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___401_21625.umax_heuristic_ok);
                                     tcenv = (uu___401_21625.tcenv);
                                     wl_implicits =
                                       (uu___401_21625.wl_implicits)
                                   })
                                 in
                              solve env uu____21616  in
                            (match uu____21615 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21629 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21635,uu____21636) ->
                  let head1 =
                    let uu____21660 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21660
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21706 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21706
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21752 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21752
                    then
                      let uu____21753 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21754 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21755 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21753 uu____21754 uu____21755
                    else ());
                   (let no_free_uvars t =
                      (let uu____21765 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21765) &&
                        (let uu____21769 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21769)
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
                      let uu____21785 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21785 = FStar_Syntax_Util.Equal  in
                    let uu____21786 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21786
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____21787 = equal t1 t2  in
                         (if uu____21787
                          then
                            let uu____21788 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____21788
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____21791 =
                            let uu____21798 = equal t1 t2  in
                            if uu____21798
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____21808 = mk_eq2 wl orig t1 t2  in
                               match uu____21808 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____21791 with
                          | (guard,wl1) ->
                              let uu____21829 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____21829))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21831,uu____21832) ->
                  let head1 =
                    let uu____21840 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21840
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21886 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21886
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21932 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21932
                    then
                      let uu____21933 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21934 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21935 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21933 uu____21934 uu____21935
                    else ());
                   (let no_free_uvars t =
                      (let uu____21945 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21945) &&
                        (let uu____21949 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21949)
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
                      let uu____21965 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21965 = FStar_Syntax_Util.Equal  in
                    let uu____21966 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21966
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____21967 = equal t1 t2  in
                         (if uu____21967
                          then
                            let uu____21968 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____21968
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____21971 =
                            let uu____21978 = equal t1 t2  in
                            if uu____21978
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____21988 = mk_eq2 wl orig t1 t2  in
                               match uu____21988 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____21971 with
                          | (guard,wl1) ->
                              let uu____22009 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22009))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____22011,uu____22012) ->
                  let head1 =
                    let uu____22014 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22014
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22060 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22060
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22106 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22106
                    then
                      let uu____22107 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22108 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22109 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22107 uu____22108 uu____22109
                    else ());
                   (let no_free_uvars t =
                      (let uu____22119 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22119) &&
                        (let uu____22123 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22123)
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
                      let uu____22139 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22139 = FStar_Syntax_Util.Equal  in
                    let uu____22140 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22140
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22141 = equal t1 t2  in
                         (if uu____22141
                          then
                            let uu____22142 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22142
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22145 =
                            let uu____22152 = equal t1 t2  in
                            if uu____22152
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22162 = mk_eq2 wl orig t1 t2  in
                               match uu____22162 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22145 with
                          | (guard,wl1) ->
                              let uu____22183 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22183))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____22185,uu____22186) ->
                  let head1 =
                    let uu____22188 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22188
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22234 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22234
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22280 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22280
                    then
                      let uu____22281 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22282 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22283 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22281 uu____22282 uu____22283
                    else ());
                   (let no_free_uvars t =
                      (let uu____22293 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22293) &&
                        (let uu____22297 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22297)
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
                      let uu____22313 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22313 = FStar_Syntax_Util.Equal  in
                    let uu____22314 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22314
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22315 = equal t1 t2  in
                         (if uu____22315
                          then
                            let uu____22316 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22316
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22319 =
                            let uu____22326 = equal t1 t2  in
                            if uu____22326
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22336 = mk_eq2 wl orig t1 t2  in
                               match uu____22336 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22319 with
                          | (guard,wl1) ->
                              let uu____22357 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22357))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____22359,uu____22360) ->
                  let head1 =
                    let uu____22362 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22362
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22408 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22408
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22454 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22454
                    then
                      let uu____22455 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22456 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22457 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22455 uu____22456 uu____22457
                    else ());
                   (let no_free_uvars t =
                      (let uu____22467 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22467) &&
                        (let uu____22471 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22471)
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
                      let uu____22487 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22487 = FStar_Syntax_Util.Equal  in
                    let uu____22488 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22488
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22489 = equal t1 t2  in
                         (if uu____22489
                          then
                            let uu____22490 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22490
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22493 =
                            let uu____22500 = equal t1 t2  in
                            if uu____22500
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22510 = mk_eq2 wl orig t1 t2  in
                               match uu____22510 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22493 with
                          | (guard,wl1) ->
                              let uu____22531 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22531))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22533,uu____22534) ->
                  let head1 =
                    let uu____22552 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22552
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22598 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22598
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22644 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22644
                    then
                      let uu____22645 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22646 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22647 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22645 uu____22646 uu____22647
                    else ());
                   (let no_free_uvars t =
                      (let uu____22657 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22657) &&
                        (let uu____22661 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22661)
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
                      let uu____22677 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22677 = FStar_Syntax_Util.Equal  in
                    let uu____22678 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22678
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22679 = equal t1 t2  in
                         (if uu____22679
                          then
                            let uu____22680 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22680
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22683 =
                            let uu____22690 = equal t1 t2  in
                            if uu____22690
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22700 = mk_eq2 wl orig t1 t2  in
                               match uu____22700 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22683 with
                          | (guard,wl1) ->
                              let uu____22721 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22721))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22723,FStar_Syntax_Syntax.Tm_match uu____22724) ->
                  let head1 =
                    let uu____22748 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22748
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22794 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22794
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22840 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22840
                    then
                      let uu____22841 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22842 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22843 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22841 uu____22842 uu____22843
                    else ());
                   (let no_free_uvars t =
                      (let uu____22853 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22853) &&
                        (let uu____22857 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22857)
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
                      let uu____22873 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22873 = FStar_Syntax_Util.Equal  in
                    let uu____22874 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22874
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22875 = equal t1 t2  in
                         (if uu____22875
                          then
                            let uu____22876 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22876
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22879 =
                            let uu____22886 = equal t1 t2  in
                            if uu____22886
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22896 = mk_eq2 wl orig t1 t2  in
                               match uu____22896 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22879 with
                          | (guard,wl1) ->
                              let uu____22917 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22917))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22919,FStar_Syntax_Syntax.Tm_uinst uu____22920) ->
                  let head1 =
                    let uu____22928 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22928
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22968 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22968
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23008 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23008
                    then
                      let uu____23009 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23010 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23011 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23009 uu____23010 uu____23011
                    else ());
                   (let no_free_uvars t =
                      (let uu____23021 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23021) &&
                        (let uu____23025 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23025)
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
                      let uu____23041 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23041 = FStar_Syntax_Util.Equal  in
                    let uu____23042 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23042
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23043 = equal t1 t2  in
                         (if uu____23043
                          then
                            let uu____23044 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23044
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23047 =
                            let uu____23054 = equal t1 t2  in
                            if uu____23054
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23064 = mk_eq2 wl orig t1 t2  in
                               match uu____23064 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23047 with
                          | (guard,wl1) ->
                              let uu____23085 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23085))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23087,FStar_Syntax_Syntax.Tm_name uu____23088) ->
                  let head1 =
                    let uu____23090 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23090
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23130 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23130
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23170 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23170
                    then
                      let uu____23171 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23172 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23173 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23171 uu____23172 uu____23173
                    else ());
                   (let no_free_uvars t =
                      (let uu____23183 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23183) &&
                        (let uu____23187 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23187)
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
                      let uu____23203 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23203 = FStar_Syntax_Util.Equal  in
                    let uu____23204 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23204
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23205 = equal t1 t2  in
                         (if uu____23205
                          then
                            let uu____23206 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23206
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23209 =
                            let uu____23216 = equal t1 t2  in
                            if uu____23216
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23226 = mk_eq2 wl orig t1 t2  in
                               match uu____23226 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23209 with
                          | (guard,wl1) ->
                              let uu____23247 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23247))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23249,FStar_Syntax_Syntax.Tm_constant uu____23250) ->
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
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23366
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23367 = equal t1 t2  in
                         (if uu____23367
                          then
                            let uu____23368 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23368
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23371 =
                            let uu____23378 = equal t1 t2  in
                            if uu____23378
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23388 = mk_eq2 wl orig t1 t2  in
                               match uu____23388 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23371 with
                          | (guard,wl1) ->
                              let uu____23409 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23409))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23411,FStar_Syntax_Syntax.Tm_fvar uu____23412) ->
                  let head1 =
                    let uu____23414 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23414
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23454 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23454
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23494 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23494
                    then
                      let uu____23495 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23496 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23497 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23495 uu____23496 uu____23497
                    else ());
                   (let no_free_uvars t =
                      (let uu____23507 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23507) &&
                        (let uu____23511 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23511)
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
                      let uu____23527 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23527 = FStar_Syntax_Util.Equal  in
                    let uu____23528 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23528
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23529 = equal t1 t2  in
                         (if uu____23529
                          then
                            let uu____23530 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23530
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23533 =
                            let uu____23540 = equal t1 t2  in
                            if uu____23540
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23550 = mk_eq2 wl orig t1 t2  in
                               match uu____23550 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23533 with
                          | (guard,wl1) ->
                              let uu____23571 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23571))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23573,FStar_Syntax_Syntax.Tm_app uu____23574) ->
                  let head1 =
                    let uu____23592 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23592
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23632 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23632
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23672 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23672
                    then
                      let uu____23673 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23674 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23675 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23673 uu____23674 uu____23675
                    else ());
                   (let no_free_uvars t =
                      (let uu____23685 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23685) &&
                        (let uu____23689 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23689)
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
                      let uu____23705 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23705 = FStar_Syntax_Util.Equal  in
                    let uu____23706 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23706
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23707 = equal t1 t2  in
                         (if uu____23707
                          then
                            let uu____23708 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23708
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23711 =
                            let uu____23718 = equal t1 t2  in
                            if uu____23718
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23728 = mk_eq2 wl orig t1 t2  in
                               match uu____23728 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23711 with
                          | (guard,wl1) ->
                              let uu____23749 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23749))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23751,FStar_Syntax_Syntax.Tm_let uu____23752) ->
                  let uu____23777 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23777
                  then
                    let uu____23778 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23778
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23780,uu____23781) ->
                  let uu____23794 =
                    let uu____23799 =
                      let uu____23800 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23801 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23802 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23803 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23800 uu____23801 uu____23802 uu____23803
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23799)
                     in
                  FStar_Errors.raise_error uu____23794
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23804,FStar_Syntax_Syntax.Tm_let uu____23805) ->
                  let uu____23818 =
                    let uu____23823 =
                      let uu____23824 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23825 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23826 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23827 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23824 uu____23825 uu____23826 uu____23827
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23823)
                     in
                  FStar_Errors.raise_error uu____23818
                    t1.FStar_Syntax_Syntax.pos
              | uu____23828 -> giveup env "head tag mismatch" orig))))

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
          (let uu____23889 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23889
           then
             let uu____23890 =
               let uu____23891 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23891  in
             let uu____23892 =
               let uu____23893 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23893  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23890 uu____23892
           else ());
          (let uu____23895 =
             let uu____23896 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23896  in
           if uu____23895
           then
             let uu____23897 =
               let uu____23898 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23899 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23898 uu____23899
                in
             giveup env uu____23897 orig
           else
             (let uu____23901 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23901 with
              | (ret_sub_prob,wl1) ->
                  let uu____23908 =
                    FStar_List.fold_right2
                      (fun uu____23945  ->
                         fun uu____23946  ->
                           fun uu____23947  ->
                             match (uu____23945, uu____23946, uu____23947)
                             with
                             | ((a1,uu____23991),(a2,uu____23993),(arg_sub_probs,wl2))
                                 ->
                                 let uu____24026 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____24026 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23908 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____24055 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____24055  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____24063 = attempt sub_probs wl3  in
                       solve env uu____24063)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____24086 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____24089)::[] -> wp1
              | uu____24114 ->
                  let uu____24125 =
                    let uu____24126 =
                      let uu____24127 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____24127  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____24126
                     in
                  failwith uu____24125
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____24133 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____24133]
              | x -> x  in
            let uu____24135 =
              let uu____24146 =
                let uu____24155 =
                  let uu____24156 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____24156 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____24155  in
              [uu____24146]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____24135;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____24173 = lift_c1 ()  in solve_eq uu____24173 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___345_24179  ->
                       match uu___345_24179 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____24180 -> false))
                in
             let uu____24181 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____24211)::uu____24212,(wp2,uu____24214)::uu____24215)
                   -> (wp1, wp2)
               | uu____24288 ->
                   let uu____24313 =
                     let uu____24318 =
                       let uu____24319 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____24320 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____24319 uu____24320
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____24318)
                      in
                   FStar_Errors.raise_error uu____24313
                     env.FStar_TypeChecker_Env.range
                in
             match uu____24181 with
             | (wpc1,wpc2) ->
                 let uu____24327 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____24327
                 then
                   let uu____24330 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____24330 wl
                 else
                   (let uu____24332 =
                      let uu____24339 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____24339  in
                    match uu____24332 with
                    | (c2_decl,qualifiers) ->
                        let uu____24360 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____24360
                        then
                          let c1_repr =
                            let uu____24364 =
                              let uu____24365 =
                                let uu____24366 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____24366  in
                              let uu____24367 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24365 uu____24367
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24364
                             in
                          let c2_repr =
                            let uu____24369 =
                              let uu____24370 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____24371 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24370 uu____24371
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24369
                             in
                          let uu____24372 =
                            let uu____24377 =
                              let uu____24378 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____24379 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____24378 uu____24379
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____24377
                             in
                          (match uu____24372 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____24383 = attempt [prob] wl2  in
                               solve env uu____24383)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____24394 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24394
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____24397 =
                                     let uu____24404 =
                                       let uu____24405 =
                                         let uu____24422 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____24425 =
                                           let uu____24436 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____24445 =
                                             let uu____24456 =
                                               let uu____24465 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____24465
                                                in
                                             [uu____24456]  in
                                           uu____24436 :: uu____24445  in
                                         (uu____24422, uu____24425)  in
                                       FStar_Syntax_Syntax.Tm_app uu____24405
                                        in
                                     FStar_Syntax_Syntax.mk uu____24404  in
                                   uu____24397 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____24516 =
                                    let uu____24523 =
                                      let uu____24524 =
                                        let uu____24541 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____24544 =
                                          let uu____24555 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24564 =
                                            let uu____24575 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24584 =
                                              let uu____24595 =
                                                let uu____24604 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24604
                                                 in
                                              [uu____24595]  in
                                            uu____24575 :: uu____24584  in
                                          uu____24555 :: uu____24564  in
                                        (uu____24541, uu____24544)  in
                                      FStar_Syntax_Syntax.Tm_app uu____24524
                                       in
                                    FStar_Syntax_Syntax.mk uu____24523  in
                                  uu____24516 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24661 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24661
                            then
                              let uu____24662 =
                                let uu____24663 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24663
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24662
                            else ());
                           (let uu____24665 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24665 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24673 =
                                    let uu____24676 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24676
                                     in
                                  solve_prob orig uu____24673 [] wl1  in
                                let uu____24679 = attempt [base_prob] wl2  in
                                solve env uu____24679))))
           in
        let uu____24680 = FStar_Util.physical_equality c1 c2  in
        if uu____24680
        then
          let uu____24681 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24681
        else
          ((let uu____24684 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24684
            then
              let uu____24685 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24686 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24685
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24686
            else ());
           (let uu____24688 =
              let uu____24697 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24700 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24697, uu____24700)  in
            match uu____24688 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24718),FStar_Syntax_Syntax.Total
                    (t2,uu____24720)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24737 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24737 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24738,FStar_Syntax_Syntax.Total uu____24739) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24757),FStar_Syntax_Syntax.Total
                    (t2,uu____24759)) ->
                     let uu____24776 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24776 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24778),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24780)) ->
                     let uu____24797 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24797 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24799),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24801)) ->
                     let uu____24818 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24818 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24819,FStar_Syntax_Syntax.Comp uu____24820) ->
                     let uu____24829 =
                       let uu___402_24832 = problem  in
                       let uu____24835 =
                         let uu____24836 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24836
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___402_24832.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24835;
                         FStar_TypeChecker_Common.relation =
                           (uu___402_24832.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___402_24832.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___402_24832.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___402_24832.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___402_24832.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___402_24832.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___402_24832.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___402_24832.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24829 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24837,FStar_Syntax_Syntax.Comp uu____24838) ->
                     let uu____24847 =
                       let uu___402_24850 = problem  in
                       let uu____24853 =
                         let uu____24854 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24854
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___402_24850.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24853;
                         FStar_TypeChecker_Common.relation =
                           (uu___402_24850.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___402_24850.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___402_24850.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___402_24850.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___402_24850.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___402_24850.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___402_24850.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___402_24850.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24847 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24855,FStar_Syntax_Syntax.GTotal uu____24856) ->
                     let uu____24865 =
                       let uu___403_24868 = problem  in
                       let uu____24871 =
                         let uu____24872 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24872
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___403_24868.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___403_24868.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___403_24868.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24871;
                         FStar_TypeChecker_Common.element =
                           (uu___403_24868.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___403_24868.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___403_24868.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___403_24868.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___403_24868.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___403_24868.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24865 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24873,FStar_Syntax_Syntax.Total uu____24874) ->
                     let uu____24883 =
                       let uu___403_24886 = problem  in
                       let uu____24889 =
                         let uu____24890 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24890
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___403_24886.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___403_24886.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___403_24886.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24889;
                         FStar_TypeChecker_Common.element =
                           (uu___403_24886.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___403_24886.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___403_24886.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___403_24886.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___403_24886.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___403_24886.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24883 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24891,FStar_Syntax_Syntax.Comp uu____24892) ->
                     let uu____24893 =
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
                     if uu____24893
                     then
                       let uu____24894 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24894 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24898 =
                            let uu____24903 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24903
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24909 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24910 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24909, uu____24910))
                             in
                          match uu____24898 with
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
                           (let uu____24917 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24917
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24919 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24919 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24922 =
                                  let uu____24923 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24924 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24923 uu____24924
                                   in
                                giveup env uu____24922 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24931 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24931 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24972 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24972 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24990 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____25018  ->
                match uu____25018 with
                | (u1,u2) ->
                    let uu____25025 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____25026 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____25025 uu____25026))
         in
      FStar_All.pipe_right uu____24990 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____25053,[])) when
          let uu____25078 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____25078 -> "{}"
      | uu____25079 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____25102 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____25102
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____25105 =
              FStar_List.map
                (fun uu____25115  ->
                   match uu____25115 with
                   | (uu____25120,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____25105 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____25125 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____25125 imps
  
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
                  let uu____25178 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____25178
                  then
                    let uu____25179 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____25180 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____25179
                      (rel_to_string rel) uu____25180
                  else "TOP"  in
                let uu____25182 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____25182 with
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
              let uu____25240 =
                let uu____25243 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____25243
                 in
              FStar_Syntax_Syntax.new_bv uu____25240 t1  in
            let uu____25246 =
              let uu____25251 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____25251
               in
            match uu____25246 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____25324 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____25324
              then
                let uu____25325 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____25325
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
          ((let uu____25347 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____25347
            then
              let uu____25348 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____25348
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____25352 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____25352
             then
               let uu____25353 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____25353
             else ());
            (let f2 =
               let uu____25356 =
                 let uu____25357 = FStar_Syntax_Util.unmeta f1  in
                 uu____25357.FStar_Syntax_Syntax.n  in
               match uu____25356 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____25361 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___404_25362 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___404_25362.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___404_25362.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___404_25362.FStar_TypeChecker_Env.implicits)
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
            let uu____25416 =
              let uu____25417 =
                let uu____25418 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____25418;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____25417  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____25416
  
let with_guard_no_simp :
  'Auu____25433 .
    'Auu____25433 ->
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
            let uu____25456 =
              let uu____25457 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____25457;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____25456
  
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
          (let uu____25487 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____25487
           then
             let uu____25488 = FStar_Syntax_Print.term_to_string t1  in
             let uu____25489 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____25488
               uu____25489
           else ());
          (let uu____25491 =
             let uu____25496 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____25496
              in
           match uu____25491 with
           | (prob,wl) ->
               let g =
                 let uu____25504 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____25514  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____25504  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25548 = try_teq true env t1 t2  in
        match uu____25548 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25552 = FStar_TypeChecker_Env.get_range env  in
              let uu____25553 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25552 uu____25553);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25560 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25560
              then
                let uu____25561 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25562 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25563 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25561
                  uu____25562 uu____25563
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
          let uu____25585 = FStar_TypeChecker_Env.get_range env  in
          let uu____25586 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25585 uu____25586
  
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
        (let uu____25611 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25611
         then
           let uu____25612 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25613 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25612 uu____25613
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25616 =
           let uu____25623 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25623 "sub_comp"
            in
         match uu____25616 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25634 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25644  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25634)))
  
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
      fun uu____25689  ->
        match uu____25689 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25732 =
                 let uu____25737 =
                   let uu____25738 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25739 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25738 uu____25739
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25737)  in
               let uu____25740 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25732 uu____25740)
               in
            let equiv1 v1 v' =
              let uu____25752 =
                let uu____25757 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25758 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25757, uu____25758)  in
              match uu____25752 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25777 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25807 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25807 with
                      | FStar_Syntax_Syntax.U_unif uu____25814 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25843  ->
                                    match uu____25843 with
                                    | (u,v') ->
                                        let uu____25852 = equiv1 v1 v'  in
                                        if uu____25852
                                        then
                                          let uu____25855 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25855 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25871 -> []))
               in
            let uu____25876 =
              let wl =
                let uu___405_25880 = empty_worklist env  in
                {
                  attempting = (uu___405_25880.attempting);
                  wl_deferred = (uu___405_25880.wl_deferred);
                  ctr = (uu___405_25880.ctr);
                  defer_ok = false;
                  smt_ok = (uu___405_25880.smt_ok);
                  umax_heuristic_ok = (uu___405_25880.umax_heuristic_ok);
                  tcenv = (uu___405_25880.tcenv);
                  wl_implicits = (uu___405_25880.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25898  ->
                      match uu____25898 with
                      | (lb,v1) ->
                          let uu____25905 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25905 with
                           | USolved wl1 -> ()
                           | uu____25907 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25917 =
              match uu____25917 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25926) -> true
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
                      uu____25949,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25951,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25962) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25969,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25977 -> false)
               in
            let uu____25982 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____25997  ->
                      match uu____25997 with
                      | (u,v1) ->
                          let uu____26004 = check_ineq (u, v1)  in
                          if uu____26004
                          then true
                          else
                            ((let uu____26007 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____26007
                              then
                                let uu____26008 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____26009 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____26008
                                  uu____26009
                              else ());
                             false)))
               in
            if uu____25982
            then ()
            else
              ((let uu____26013 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____26013
                then
                  ((let uu____26015 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____26015);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____26025 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____26025))
                else ());
               (let uu____26035 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____26035))
  
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
        let fail1 uu____26102 =
          match uu____26102 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___406_26123 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___406_26123.attempting);
            wl_deferred = (uu___406_26123.wl_deferred);
            ctr = (uu___406_26123.ctr);
            defer_ok;
            smt_ok = (uu___406_26123.smt_ok);
            umax_heuristic_ok = (uu___406_26123.umax_heuristic_ok);
            tcenv = (uu___406_26123.tcenv);
            wl_implicits = (uu___406_26123.wl_implicits)
          }  in
        (let uu____26125 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26125
         then
           let uu____26126 = FStar_Util.string_of_bool defer_ok  in
           let uu____26127 = wl_to_string wl  in
           let uu____26128 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____26126 uu____26127 uu____26128
         else ());
        (let g1 =
           let uu____26131 = solve_and_commit env wl fail1  in
           match uu____26131 with
           | FStar_Pervasives_Native.Some
               (uu____26138::uu____26139,uu____26140) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___407_26165 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___407_26165.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___407_26165.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____26166 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___408_26174 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___408_26174.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___408_26174.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___408_26174.FStar_TypeChecker_Env.implicits)
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
    let uu____26222 = FStar_ST.op_Bang last_proof_ns  in
    match uu____26222 with
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
            let uu___409_26333 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___409_26333.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___409_26333.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___409_26333.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____26334 =
            let uu____26335 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____26335  in
          if uu____26334
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____26343 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____26344 =
                       let uu____26345 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____26345
                        in
                     FStar_Errors.diag uu____26343 uu____26344)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____26349 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____26350 =
                        let uu____26351 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____26351
                         in
                      FStar_Errors.diag uu____26349 uu____26350)
                   else ();
                   (let uu____26354 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____26354
                      "discharge_guard'" env vc1);
                   (let uu____26355 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____26355 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____26362 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26363 =
                                let uu____26364 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____26364
                                 in
                              FStar_Errors.diag uu____26362 uu____26363)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____26369 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26370 =
                                let uu____26371 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____26371
                                 in
                              FStar_Errors.diag uu____26369 uu____26370)
                           else ();
                           (let vcs =
                              let uu____26382 = FStar_Options.use_tactics ()
                                 in
                              if uu____26382
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____26402  ->
                                     (let uu____26404 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a235  -> ())
                                        uu____26404);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____26447  ->
                                              match uu____26447 with
                                              | (env1,goal,opts) ->
                                                  let uu____26463 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____26463, opts)))))
                              else
                                (let uu____26465 =
                                   let uu____26472 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____26472)  in
                                 [uu____26465])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____26505  ->
                                    match uu____26505 with
                                    | (env1,goal,opts) ->
                                        let uu____26515 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____26515 with
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
                                                (let uu____26523 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26524 =
                                                   let uu____26525 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____26526 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____26525 uu____26526
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26523 uu____26524)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____26529 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26530 =
                                                   let uu____26531 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____26531
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26529 uu____26530)
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
      let uu____26545 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26545 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26552 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26552
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26563 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26563 with
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
        let uu____26589 = try_teq false env t1 t2  in
        match uu____26589 with
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
            let uu____26624 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26624 with
            | FStar_Pervasives_Native.Some uu____26627 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26647 = acc  in
            match uu____26647 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26659 = hd1  in
                     (match uu____26659 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26664;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26672 = unresolved ctx_u  in
                             if uu____26672
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
                                     let uu____26687 = teq_nosmt env1 t tm
                                        in
                                     match uu____26687 with
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "resolve_implicits: unifying with an unresolved uvar failed?"
                                     | FStar_Pervasives_Native.Some g1 ->
                                         g1.FStar_TypeChecker_Env.implicits
                                      in
                                   let hd2 =
                                     let uu___410_26696 = hd1  in
                                     {
                                       FStar_TypeChecker_Env.imp_reason =
                                         (uu___410_26696.FStar_TypeChecker_Env.imp_reason);
                                       FStar_TypeChecker_Env.imp_uvar =
                                         (uu___410_26696.FStar_TypeChecker_Env.imp_uvar);
                                       FStar_TypeChecker_Env.imp_tm =
                                         (uu___410_26696.FStar_TypeChecker_Env.imp_tm);
                                       FStar_TypeChecker_Env.imp_range =
                                         (uu___410_26696.FStar_TypeChecker_Env.imp_range);
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
                                    let uu___411_26704 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___411_26704.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___411_26704.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___411_26704.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___411_26704.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___411_26704.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___411_26704.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___411_26704.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___411_26704.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___411_26704.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___411_26704.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___411_26704.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___411_26704.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___411_26704.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___411_26704.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___411_26704.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___411_26704.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___411_26704.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___411_26704.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___411_26704.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___411_26704.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___411_26704.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___411_26704.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___411_26704.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___411_26704.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___411_26704.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___411_26704.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___411_26704.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___411_26704.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___411_26704.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___411_26704.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___411_26704.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___411_26704.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___411_26704.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___411_26704.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___411_26704.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___411_26704.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___411_26704.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___411_26704.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___411_26704.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___411_26704.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___411_26704.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___411_26704.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___412_26707 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___412_26707.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___412_26707.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___412_26707.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___412_26707.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___412_26707.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___412_26707.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___412_26707.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___412_26707.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___412_26707.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___412_26707.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___412_26707.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___412_26707.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___412_26707.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___412_26707.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___412_26707.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___412_26707.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___412_26707.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___412_26707.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___412_26707.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___412_26707.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___412_26707.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___412_26707.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___412_26707.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___412_26707.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___412_26707.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___412_26707.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___412_26707.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___412_26707.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___412_26707.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___412_26707.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___412_26707.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___412_26707.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___412_26707.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___412_26707.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___412_26707.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___412_26707.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___412_26707.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___412_26707.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___412_26707.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___412_26707.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___412_26707.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___412_26707.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26710 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26710
                                   then
                                     let uu____26711 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26712 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26713 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26714 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26711 uu____26712 uu____26713
                                       reason uu____26714
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___414_26718  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26725 =
                                             let uu____26734 =
                                               let uu____26741 =
                                                 let uu____26742 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26743 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26744 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26742 uu____26743
                                                   uu____26744
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26741, r)
                                                in
                                             [uu____26734]  in
                                           FStar_Errors.add_errors
                                             uu____26725);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___415_26758 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___415_26758.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___415_26758.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___415_26758.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26761 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26771  ->
                                               let uu____26772 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26773 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26774 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26772 uu____26773
                                                 reason uu____26774)) env2 g2
                                         true
                                        in
                                     match uu____26761 with
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
          let uu___416_26776 = g  in
          let uu____26777 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___416_26776.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___416_26776.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___416_26776.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26777
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
        let uu____26811 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26811 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26812 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a236  -> ()) uu____26812
      | imp::uu____26814 ->
          let uu____26817 =
            let uu____26822 =
              let uu____26823 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26824 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26823 uu____26824 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26822)
             in
          FStar_Errors.raise_error uu____26817
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26840 = teq_nosmt env t1 t2  in
        match uu____26840 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___417_26855 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___417_26855.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___417_26855.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___417_26855.FStar_TypeChecker_Env.implicits)
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
        (let uu____26890 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26890
         then
           let uu____26891 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26892 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26891
             uu____26892
         else ());
        (let uu____26894 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26894 with
         | (prob,x,wl) ->
             let g =
               let uu____26913 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26923  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26913  in
             ((let uu____26943 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26943
               then
                 let uu____26944 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26945 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26946 =
                   let uu____26947 = FStar_Util.must g  in
                   guard_to_string env uu____26947  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26944 uu____26945 uu____26946
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
        let uu____26981 = check_subtyping env t1 t2  in
        match uu____26981 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____27000 =
              let uu____27001 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____27001 g  in
            FStar_Pervasives_Native.Some uu____27000
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____27019 = check_subtyping env t1 t2  in
        match uu____27019 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____27038 =
              let uu____27039 =
                let uu____27040 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____27040]  in
              FStar_TypeChecker_Env.close_guard env uu____27039 g  in
            FStar_Pervasives_Native.Some uu____27038
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____27077 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____27077
         then
           let uu____27078 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____27079 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____27078
             uu____27079
         else ());
        (let uu____27081 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____27081 with
         | (prob,x,wl) ->
             let g =
               let uu____27096 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____27106  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____27096  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____27129 =
                      let uu____27130 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____27130]  in
                    FStar_TypeChecker_Env.close_guard env uu____27129 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____27167 = subtype_nosmt env t1 t2  in
        match uu____27167 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  