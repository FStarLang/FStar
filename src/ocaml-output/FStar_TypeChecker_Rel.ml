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
                 (ctx_uvar, t,
                   (let uu___337_381 = wl  in
                    {
                      attempting = (uu___337_381.attempting);
                      wl_deferred = (uu___337_381.wl_deferred);
                      ctr = (uu___337_381.ctr);
                      defer_ok = (uu___337_381.defer_ok);
                      smt_ok = (uu___337_381.smt_ok);
                      tcenv = (uu___337_381.tcenv);
                      wl_implicits = ((reason, t, ctx_uvar, r) ::
                        (wl.wl_implicits))
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
            let uu___338_421 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___338_421.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___338_421.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___338_421.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___338_421.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___338_421.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___338_421.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___338_421.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___338_421.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___338_421.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___338_421.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___338_421.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___338_421.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___338_421.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___338_421.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___338_421.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___338_421.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___338_421.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___338_421.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___338_421.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___338_421.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___338_421.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___338_421.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___338_421.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___338_421.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___338_421.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___338_421.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___338_421.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___338_421.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___338_421.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___338_421.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___338_421.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___338_421.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___338_421.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___338_421.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___338_421.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___338_421.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___338_421.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___338_421.FStar_TypeChecker_Env.dep_graph);
              FStar_TypeChecker_Env.nbe =
                (uu___338_421.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____423 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____423 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____458 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____488 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____513 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____519 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____525 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___303_540  ->
    match uu___303_540 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____546 = FStar_Syntax_Util.head_and_args t  in
    match uu____546 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____601 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____602 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____614 =
                     let uu____615 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____615  in
                   FStar_Util.format1 "@<%s>" uu____614
                in
             let uu____618 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____601 uu____602 uu____618
         | uu____619 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___304_629  ->
      match uu___304_629 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____633 =
            let uu____636 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____637 =
              let uu____640 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____641 =
                let uu____644 =
                  let uu____647 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____647]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____644
                 in
              uu____640 :: uu____641  in
            uu____636 :: uu____637  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____633
      | FStar_TypeChecker_Common.CProb p ->
          let uu____651 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____652 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____653 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____651 uu____652
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____653
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___305_663  ->
      match uu___305_663 with
      | UNIV (u,t) ->
          let x =
            let uu____667 = FStar_Options.hide_uvar_nums ()  in
            if uu____667
            then "?"
            else
              (let uu____669 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____669 FStar_Util.string_of_int)
             in
          let uu____670 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____670
      | TERM (u,t) ->
          let x =
            let uu____674 = FStar_Options.hide_uvar_nums ()  in
            if uu____674
            then "?"
            else
              (let uu____676 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____676 FStar_Util.string_of_int)
             in
          let uu____677 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____677
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____692 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____692 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____706 =
      let uu____709 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____709
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____706 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____722 .
    (FStar_Syntax_Syntax.term,'Auu____722) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____740 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____758  ->
              match uu____758 with
              | (x,uu____764) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____740 (FStar_String.concat " ")
  
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
        (let uu____802 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____802
         then
           let uu____803 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____803
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___306_809  ->
    match uu___306_809 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____814 .
    'Auu____814 FStar_TypeChecker_Common.problem ->
      'Auu____814 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___339_826 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___339_826.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___339_826.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___339_826.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___339_826.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___339_826.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___339_826.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___339_826.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____833 .
    'Auu____833 FStar_TypeChecker_Common.problem ->
      'Auu____833 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___307_850  ->
    match uu___307_850 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___308_865  ->
    match uu___308_865 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___340_871 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___340_871.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___340_871.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___340_871.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___340_871.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___340_871.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___340_871.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___340_871.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___340_871.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___340_871.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___341_879 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___341_879.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___341_879.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___341_879.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___341_879.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___341_879.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___341_879.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___341_879.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___341_879.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___341_879.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___309_891  ->
      match uu___309_891 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___310_896  ->
    match uu___310_896 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___311_907  ->
    match uu___311_907 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___312_920  ->
    match uu___312_920 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___313_933  ->
    match uu___313_933 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___314_946  ->
    match uu___314_946 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___315_959  ->
    match uu___315_959 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___316_970  ->
    match uu___316_970 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____985 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____985) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1013 =
          let uu____1014 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1014  in
        if uu____1013
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1048)::bs ->
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
          let uu____1088 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1106 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1106]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1088
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1126 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1144 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1144]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1126
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1177 =
          let uu____1178 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1178  in
        if uu____1177
        then ()
        else
          (let uu____1180 =
             let uu____1183 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1183
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1180 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1221 =
          let uu____1222 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1222  in
        if uu____1221
        then ()
        else
          (let uu____1224 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1224)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1239 =
        let uu____1240 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1240  in
      if uu____1239
      then ()
      else
        (let msgf m =
           let uu____1248 =
             let uu____1249 =
               let uu____1250 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1250 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1249  in
           Prims.strcat msg uu____1248  in
         (let uu____1252 = msgf "scope"  in
          let uu____1253 = p_scope prob  in
          def_scope_wf uu____1252 (p_loc prob) uu____1253);
         (let uu____1261 = msgf "guard"  in
          def_check_scoped uu____1261 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1266 = msgf "lhs"  in
                def_check_scoped uu____1266 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1267 = msgf "rhs"  in
                def_check_scoped uu____1267 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1272 = msgf "lhs"  in
                def_check_scoped_comp uu____1272 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1273 = msgf "rhs"  in
                def_check_scoped_comp uu____1273 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___342_1289 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___342_1289.wl_deferred);
          ctr = (uu___342_1289.ctr);
          defer_ok = (uu___342_1289.defer_ok);
          smt_ok;
          tcenv = (uu___342_1289.tcenv);
          wl_implicits = (uu___342_1289.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1296 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1296,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___343_1319 = empty_worklist env  in
      let uu____1320 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1320;
        wl_deferred = (uu___343_1319.wl_deferred);
        ctr = (uu___343_1319.ctr);
        defer_ok = (uu___343_1319.defer_ok);
        smt_ok = (uu___343_1319.smt_ok);
        tcenv = (uu___343_1319.tcenv);
        wl_implicits = (uu___343_1319.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___344_1340 = wl  in
        {
          attempting = (uu___344_1340.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___344_1340.ctr);
          defer_ok = (uu___344_1340.defer_ok);
          smt_ok = (uu___344_1340.smt_ok);
          tcenv = (uu___344_1340.tcenv);
          wl_implicits = (uu___344_1340.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___345_1362 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___345_1362.wl_deferred);
         ctr = (uu___345_1362.ctr);
         defer_ok = (uu___345_1362.defer_ok);
         smt_ok = (uu___345_1362.smt_ok);
         tcenv = (uu___345_1362.tcenv);
         wl_implicits = (uu___345_1362.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1373 .
    worklist ->
      'Auu____1373 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1402 = FStar_Syntax_Util.type_u ()  in
          match uu____1402 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1414 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1414 with
               | (uu____1425,tt,wl1) ->
                   let uu____1428 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1428, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___317_1433  ->
    match uu___317_1433 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1449 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1449 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1459  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1557 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1557 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1557 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1557 FStar_TypeChecker_Common.problem,worklist)
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
                        let uu____1634 =
                          let uu____1641 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1641]  in
                        FStar_List.append scope uu____1634
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____1672 =
                      let uu____1675 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____1675  in
                    FStar_List.append uu____1672
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____1688 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1688 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____1707 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____1707;
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
                  (let uu____1771 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1771 with
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
                  (let uu____1850 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1850 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____1886 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1886 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1886 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____1886 FStar_TypeChecker_Common.problem,worklist)
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
                          let uu____1950 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1950]  in
                        let uu____1963 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____1963
                     in
                  let uu____1966 =
                    let uu____1973 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___346_1981 = wl  in
                       {
                         attempting = (uu___346_1981.attempting);
                         wl_deferred = (uu___346_1981.wl_deferred);
                         ctr = (uu___346_1981.ctr);
                         defer_ok = (uu___346_1981.defer_ok);
                         smt_ok = (uu___346_1981.smt_ok);
                         tcenv = env;
                         wl_implicits = (uu___346_1981.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____1973
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1966 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____1993 =
                              let uu____1998 =
                                let uu____1999 =
                                  let uu____2006 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2006
                                   in
                                [uu____1999]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____1998  in
                            uu____1993 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2030 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2030;
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
                let uu____2072 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2072;
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
  'Auu____2084 .
    worklist ->
      'Auu____2084 FStar_TypeChecker_Common.problem ->
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
              let uu____2117 =
                let uu____2120 =
                  let uu____2121 =
                    let uu____2128 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2128)  in
                  FStar_Syntax_Syntax.NT uu____2121  in
                [uu____2120]  in
              FStar_Syntax_Subst.subst uu____2117 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2148 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2148
        then
          let uu____2149 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2150 = prob_to_string env d  in
          let uu____2151 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2149 uu____2150 uu____2151 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2157 -> failwith "impossible"  in
           let uu____2158 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2170 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2171 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2170, uu____2171)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2175 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2176 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2175, uu____2176)
              in
           match uu____2158 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___318_2194  ->
            match uu___318_2194 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2206 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2210 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2210 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___319_2235  ->
           match uu___319_2235 with
           | UNIV uu____2238 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2245 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2245
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
        (fun uu___320_2269  ->
           match uu___320_2269 with
           | UNIV (u',t) ->
               let uu____2274 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2274
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2278 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2289 =
        let uu____2290 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF] env uu____2290
         in
      FStar_Syntax_Subst.compress uu____2289
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2301 =
        FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
          env t
         in
      FStar_Syntax_Subst.compress uu____2301
  
let norm_arg :
  'Auu____2308 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2308) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2308)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2331 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2331, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2372  ->
              match uu____2372 with
              | (x,imp) ->
                  let uu____2383 =
                    let uu___347_2384 = x  in
                    let uu____2385 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___347_2384.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___347_2384.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2385
                    }  in
                  (uu____2383, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2406 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2406
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2410 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2410
        | uu____2413 -> u2  in
      let uu____2414 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2414
  
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
                (let uu____2536 = norm_refinement env t12  in
                 match uu____2536 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2553;
                     FStar_Syntax_Syntax.vars = uu____2554;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2580 =
                       let uu____2581 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2582 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2581 uu____2582
                        in
                     failwith uu____2580)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2598 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2598
          | FStar_Syntax_Syntax.Tm_uinst uu____2599 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2638 =
                   let uu____2639 = FStar_Syntax_Subst.compress t1'  in
                   uu____2639.FStar_Syntax_Syntax.n  in
                 match uu____2638 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2656 -> aux true t1'
                 | uu____2663 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2680 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2713 =
                   let uu____2714 = FStar_Syntax_Subst.compress t1'  in
                   uu____2714.FStar_Syntax_Syntax.n  in
                 match uu____2713 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2731 -> aux true t1'
                 | uu____2738 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2755 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2802 =
                   let uu____2803 = FStar_Syntax_Subst.compress t1'  in
                   uu____2803.FStar_Syntax_Syntax.n  in
                 match uu____2802 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2820 -> aux true t1'
                 | uu____2827 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2844 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2861 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2878 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2895 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2912 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2941 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____2974 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2997 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3026 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3055 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3094 ->
              let uu____3101 =
                let uu____3102 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3103 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3102 uu____3103
                 in
              failwith uu____3101
          | FStar_Syntax_Syntax.Tm_ascribed uu____3118 ->
              let uu____3145 =
                let uu____3146 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3147 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3146 uu____3147
                 in
              failwith uu____3145
          | FStar_Syntax_Syntax.Tm_delayed uu____3162 ->
              let uu____3185 =
                let uu____3186 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3187 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3186 uu____3187
                 in
              failwith uu____3185
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3202 =
                let uu____3203 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3204 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3203 uu____3204
                 in
              failwith uu____3202
           in
        let uu____3219 = whnf env t1  in aux false uu____3219
  
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
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
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
      let uu____3265 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3265 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3301 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3301, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3312 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3312 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3339 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3339 with
          | (t_base,refinement) ->
              (match refinement with
               | FStar_Pervasives_Native.None  -> trivial_refinement t_base
               | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                          FStar_Syntax_Syntax.term)
                                                          FStar_Pervasives_Native.tuple2
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun uu____3426  ->
    match uu____3426 with
    | (t_base,refopt) ->
        let uu____3459 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3459 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3499 =
      let uu____3502 =
        let uu____3505 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3528  ->
                  match uu____3528 with | (uu____3535,uu____3536,x) -> x))
           in
        FStar_List.append wl.attempting uu____3505  in
      FStar_List.map (wl_prob_to_string wl) uu____3502  in
    FStar_All.pipe_right uu____3499 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____3550 .
    ('Auu____3550,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3561  ->
    match uu____3561 with
    | (uu____3568,c,args) ->
        let uu____3571 = print_ctx_uvar c  in
        let uu____3572 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3571 uu____3572
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3578 = FStar_Syntax_Util.head_and_args t  in
    match uu____3578 with
    | (head1,_args) ->
        let uu____3615 =
          let uu____3616 = FStar_Syntax_Subst.compress head1  in
          uu____3616.FStar_Syntax_Syntax.n  in
        (match uu____3615 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3619 -> true
         | uu____3632 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3638 = FStar_Syntax_Util.head_and_args t  in
    match uu____3638 with
    | (head1,_args) ->
        let uu____3675 =
          let uu____3676 = FStar_Syntax_Subst.compress head1  in
          uu____3676.FStar_Syntax_Syntax.n  in
        (match uu____3675 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____3680) -> u
         | uu____3697 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____3720 = FStar_Syntax_Util.head_and_args t  in
      match uu____3720 with
      | (head1,args) ->
          let uu____3761 =
            let uu____3762 = FStar_Syntax_Subst.compress head1  in
            uu____3762.FStar_Syntax_Syntax.n  in
          (match uu____3761 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____3770)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____3803 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___321_3828  ->
                         match uu___321_3828 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____3832 =
                               let uu____3833 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____3833.FStar_Syntax_Syntax.n  in
                             (match uu____3832 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____3837 -> false)
                         | uu____3838 -> true))
                  in
               (match uu____3803 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____3860 =
                        FStar_List.collect
                          (fun uu___322_3870  ->
                             match uu___322_3870 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____3874 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____3874]
                             | uu____3875 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____3860 FStar_List.rev  in
                    let uu____3892 =
                      let uu____3899 =
                        let uu____3906 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___323_3924  ->
                                  match uu___323_3924 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____3928 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____3928]
                                  | uu____3929 -> []))
                           in
                        FStar_All.pipe_right uu____3906 FStar_List.rev  in
                      let uu____3946 =
                        let uu____3949 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____3949  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____3899 uu____3946
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____3892 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____3978  ->
                                match uu____3978 with
                                | (x,i) ->
                                    let uu____3989 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____3989, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4012  ->
                                match uu____4012 with
                                | (a,i) ->
                                    let uu____4023 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4023, i)) args_sol
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
           | uu____4039 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4059 =
          let uu____4080 =
            let uu____4081 = FStar_Syntax_Subst.compress k  in
            uu____4081.FStar_Syntax_Syntax.n  in
          match uu____4080 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4150 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4150)
              else
                (let uu____4180 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4180 with
                 | (ys',t1,uu____4211) ->
                     let uu____4216 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4216))
          | uu____4249 ->
              let uu____4250 =
                let uu____4255 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4255)  in
              ((ys, t), uu____4250)
           in
        match uu____4059 with
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
                 let uu____4332 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4332 c  in
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
               (let uu____4406 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4406
                then
                  let uu____4407 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4408 = print_ctx_uvar uv  in
                  let uu____4409 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4407 uu____4408 uu____4409
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4415 =
                   let uu____4416 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4416  in
                 let uu____4417 =
                   let uu____4420 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4420
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____4415 uu____4417 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____4445 =
               let uu____4446 =
                 let uu____4447 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____4448 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____4447 uu____4448
                  in
               failwith uu____4446  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____4498  ->
                       match uu____4498 with
                       | (a,i) ->
                           let uu____4511 =
                             let uu____4512 = FStar_Syntax_Subst.compress a
                                in
                             uu____4512.FStar_Syntax_Syntax.n  in
                           (match uu____4511 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____4530 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____4538 =
                 let uu____4539 = is_flex g  in Prims.op_Negation uu____4539
                  in
               if uu____4538
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____4543 = destruct_flex_t g wl  in
                  match uu____4543 with
                  | ((uu____4548,uv1,args),wl1) ->
                      ((let uu____4553 = args_as_binders args  in
                        assign_solution uu____4553 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___348_4555 = wl1  in
              {
                attempting = (uu___348_4555.attempting);
                wl_deferred = (uu___348_4555.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___348_4555.defer_ok);
                smt_ok = (uu___348_4555.smt_ok);
                tcenv = (uu___348_4555.tcenv);
                wl_implicits = (uu___348_4555.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4576 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4576
         then
           let uu____4577 = FStar_Util.string_of_int pid  in
           let uu____4578 =
             let uu____4579 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4579 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4577 uu____4578
         else ());
        commit sol;
        (let uu___349_4586 = wl  in
         {
           attempting = (uu___349_4586.attempting);
           wl_deferred = (uu___349_4586.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___349_4586.defer_ok);
           smt_ok = (uu___349_4586.smt_ok);
           tcenv = (uu___349_4586.tcenv);
           wl_implicits = (uu___349_4586.wl_implicits)
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
             | (uu____4648,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4676 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4676
              in
           (let uu____4682 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4682
            then
              let uu____4683 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4684 =
                let uu____4685 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4685 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4683 uu____4684
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
        let uu____4710 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4710 FStar_Util.set_elements  in
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
      let uu____4744 = occurs uk t  in
      match uu____4744 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4773 =
                 let uu____4774 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4775 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4774 uu____4775
                  in
               FStar_Pervasives_Native.Some uu____4773)
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
            let uu____4864 = maximal_prefix bs_tail bs'_tail  in
            (match uu____4864 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____4908 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____4956  ->
             match uu____4956 with
             | (x,uu____4966) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____4979 = FStar_List.last bs  in
      match uu____4979 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____4997) ->
          let uu____5002 =
            FStar_Util.prefix_until
              (fun uu___324_5017  ->
                 match uu___324_5017 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5019 -> false) g
             in
          (match uu____5002 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5032,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5068 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5068 with
        | (pfx,uu____5078) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5090 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5090 with
             | (uu____5097,src',wl1) ->
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
                 | uu____5197 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5198 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5252  ->
                  fun uu____5253  ->
                    match (uu____5252, uu____5253) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5334 =
                          let uu____5335 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5335
                           in
                        if uu____5334
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5360 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5360
                           then
                             let uu____5373 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5373)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5198 with | (isect,uu____5410) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5439 'Auu____5440 .
    (FStar_Syntax_Syntax.bv,'Auu____5439) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5440) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5497  ->
              fun uu____5498  ->
                match (uu____5497, uu____5498) with
                | ((a,uu____5516),(b,uu____5518)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5533 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5533) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5563  ->
           match uu____5563 with
           | (y,uu____5569) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5578 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5578) FStar_Pervasives_Native.tuple2
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
                   let uu____5708 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5708
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____5728 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____5771 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____5809 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5822 -> false
  
let string_of_option :
  'Auu____5829 .
    ('Auu____5829 -> Prims.string) ->
      'Auu____5829 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___325_5844  ->
      match uu___325_5844 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5850 = f x  in Prims.strcat "Some " uu____5850
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___326_5855  ->
    match uu___326_5855 with
    | MisMatch (d1,d2) ->
        let uu____5866 =
          let uu____5867 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5868 =
            let uu____5869 =
              let uu____5870 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5870 ")"  in
            Prims.strcat ") (" uu____5869  in
          Prims.strcat uu____5867 uu____5868  in
        Prims.strcat "MisMatch (" uu____5866
    | HeadMatch u ->
        let uu____5872 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____5872
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___327_5877  ->
    match uu___327_5877 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____5892 -> HeadMatch false
  
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
          let uu____5906 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5906 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____5917 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5940 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5949 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5975 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5975
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5976 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5977 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5978 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5991 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6004 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6028) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6034,uu____6035) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6077) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6098;
             FStar_Syntax_Syntax.index = uu____6099;
             FStar_Syntax_Syntax.sort = t2;_},uu____6101)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6108 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6109 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6110 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6123 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6130 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6148 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6148
  
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
            let uu____6175 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6175
            then FullMatch
            else
              (let uu____6177 =
                 let uu____6186 =
                   let uu____6189 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6189  in
                 let uu____6190 =
                   let uu____6193 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6193  in
                 (uu____6186, uu____6190)  in
               MisMatch uu____6177)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6199),FStar_Syntax_Syntax.Tm_uinst (g,uu____6201)) ->
            let uu____6210 = head_matches env f g  in
            FStar_All.pipe_right uu____6210 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6213 = FStar_Const.eq_const c d  in
            if uu____6213
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6220),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6222)) ->
            let uu____6255 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6255
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6262),FStar_Syntax_Syntax.Tm_refine (y,uu____6264)) ->
            let uu____6273 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6273 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6275),uu____6276) ->
            let uu____6281 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6281 head_match
        | (uu____6282,FStar_Syntax_Syntax.Tm_refine (x,uu____6284)) ->
            let uu____6289 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6289 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6290,FStar_Syntax_Syntax.Tm_type
           uu____6291) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6292,FStar_Syntax_Syntax.Tm_arrow uu____6293) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6319),FStar_Syntax_Syntax.Tm_app (head',uu____6321))
            ->
            let uu____6362 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6362 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6364),uu____6365) ->
            let uu____6386 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6386 head_match
        | (uu____6387,FStar_Syntax_Syntax.Tm_app (head1,uu____6389)) ->
            let uu____6410 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6410 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6411,FStar_Syntax_Syntax.Tm_let
           uu____6412) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6437,FStar_Syntax_Syntax.Tm_match uu____6438) ->
            HeadMatch true
        | uu____6483 ->
            let uu____6488 =
              let uu____6497 = delta_depth_of_term env t11  in
              let uu____6500 = delta_depth_of_term env t21  in
              (uu____6497, uu____6500)  in
            MisMatch uu____6488
  
let head_matches_delta :
  'Auu____6517 .
    FStar_TypeChecker_Env.env ->
      'Auu____6517 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                            FStar_Pervasives_Native.tuple2
                            FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let head1 = FStar_Syntax_Util.head_of t  in
            (let uu____6566 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____6566
             then
               let uu____6567 = FStar_Syntax_Print.term_to_string t  in
               let uu____6568 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____6567 uu____6568
             else ());
            (let uu____6570 =
               let uu____6571 = FStar_Syntax_Util.un_uinst head1  in
               uu____6571.FStar_Syntax_Syntax.n  in
             match uu____6570 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____6577 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____6577 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____6591 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____6591
                        then
                          let uu____6592 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____6592
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____6594 ->
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
                      ((let uu____6605 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____6605
                        then
                          let uu____6606 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____6607 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____6606
                            uu____6607
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____6609 -> FStar_Pervasives_Native.None)
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
            (let uu____6747 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____6747
             then
               let uu____6748 = FStar_Syntax_Print.term_to_string t11  in
               let uu____6749 = FStar_Syntax_Print.term_to_string t21  in
               let uu____6750 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6748
                 uu____6749 uu____6750
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____6774 =
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
               match uu____6774 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____6819 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____6819 with
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
                  uu____6851),uu____6852)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____6870 =
                      let uu____6879 = maybe_inline t11  in
                      let uu____6882 = maybe_inline t21  in
                      (uu____6879, uu____6882)  in
                    match uu____6870 with
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
                 (uu____6919,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____6920))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____6938 =
                      let uu____6947 = maybe_inline t11  in
                      let uu____6950 = maybe_inline t21  in
                      (uu____6947, uu____6950)  in
                    match uu____6938 with
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
             | MisMatch uu____6999 -> fail1 n_delta r t11 t21
             | uu____7008 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7021 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7021
           then
             let uu____7022 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7023 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7024 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7031 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7049 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7049
                    (fun uu____7083  ->
                       match uu____7083 with
                       | (t11,t21) ->
                           let uu____7090 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7091 =
                             let uu____7092 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7092  in
                           Prims.strcat uu____7090 uu____7091))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7022 uu____7023 uu____7024 uu____7031
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7104 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7104 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___328_7117  ->
    match uu___328_7117 with
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
      let uu___350_7154 = p  in
      let uu____7157 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7158 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___350_7154.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7157;
        FStar_TypeChecker_Common.relation =
          (uu___350_7154.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7158;
        FStar_TypeChecker_Common.element =
          (uu___350_7154.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___350_7154.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___350_7154.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___350_7154.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___350_7154.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___350_7154.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7172 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7172
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7177 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7199 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7199 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7207 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7207 with
           | (lh,lhs_args) ->
               let uu____7248 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7248 with
                | (rh,rhs_args) ->
                    let uu____7289 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7302,FStar_Syntax_Syntax.Tm_uvar uu____7303)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7380 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7403,uu____7404)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7419,FStar_Syntax_Syntax.Tm_uvar uu____7420)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7435,FStar_Syntax_Syntax.Tm_arrow uu____7436)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___351_7464 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___351_7464.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___351_7464.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___351_7464.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___351_7464.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___351_7464.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___351_7464.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___351_7464.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___351_7464.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___351_7464.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7467,FStar_Syntax_Syntax.Tm_type uu____7468)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___351_7484 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___351_7484.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___351_7484.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___351_7484.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___351_7484.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___351_7484.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___351_7484.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___351_7484.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___351_7484.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___351_7484.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7487,FStar_Syntax_Syntax.Tm_uvar uu____7488)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___351_7504 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___351_7504.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___351_7504.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___351_7504.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___351_7504.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___351_7504.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___351_7504.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___351_7504.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___351_7504.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___351_7504.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7507,FStar_Syntax_Syntax.Tm_uvar uu____7508)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7523,uu____7524)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7539,FStar_Syntax_Syntax.Tm_uvar uu____7540)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7555,uu____7556) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7289 with
                     | (rank,tp1) ->
                         let uu____7569 =
                           FStar_All.pipe_right
                             (let uu___352_7573 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___352_7573.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___352_7573.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___352_7573.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___352_7573.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___352_7573.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___352_7573.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___352_7573.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___352_7573.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___352_7573.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____7569))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7579 =
            FStar_All.pipe_right
              (let uu___353_7583 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___353_7583.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___353_7583.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___353_7583.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___353_7583.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___353_7583.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___353_7583.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___353_7583.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___353_7583.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___353_7583.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7579)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____7644 probs =
      match uu____7644 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____7725 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____7746 = rank wl.tcenv hd1  in
               (match uu____7746 with
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
                      (let uu____7805 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7809 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____7809)
                          in
                       if uu____7805
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
          let uu____7877 = FStar_Syntax_Util.head_and_args t  in
          match uu____7877 with
          | (hd1,uu____7893) ->
              let uu____7914 =
                let uu____7915 = FStar_Syntax_Subst.compress hd1  in
                uu____7915.FStar_Syntax_Syntax.n  in
              (match uu____7914 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____7919) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____7949  ->
                           match uu____7949 with
                           | (y,uu____7955) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____7969  ->
                                       match uu____7969 with
                                       | (x,uu____7975) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____7976 -> false)
           in
        let uu____7977 = rank tcenv p  in
        match uu____7977 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____7984 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8011 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8025 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8039 -> false
  
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
                        let uu____8091 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8091 with
                        | (k,uu____8097) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8107 -> false)))
            | uu____8108 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8160 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8166 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8166 = (Prims.parse_int "0")))
                           in
                        if uu____8160 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8182 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8188 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8188 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8182)
               in
            let uu____8189 = filter1 u12  in
            let uu____8192 = filter1 u22  in (uu____8189, uu____8192)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8221 = filter_out_common_univs us1 us2  in
                (match uu____8221 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8280 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8280 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8283 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8293 =
                          let uu____8294 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8295 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8294
                            uu____8295
                           in
                        UFailed uu____8293))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8319 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8319 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8345 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8345 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8348 ->
                let uu____8353 =
                  let uu____8354 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8355 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8354
                    uu____8355 msg
                   in
                UFailed uu____8353
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8356,uu____8357) ->
              let uu____8358 =
                let uu____8359 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8360 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8359 uu____8360
                 in
              failwith uu____8358
          | (FStar_Syntax_Syntax.U_unknown ,uu____8361) ->
              let uu____8362 =
                let uu____8363 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8364 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8363 uu____8364
                 in
              failwith uu____8362
          | (uu____8365,FStar_Syntax_Syntax.U_bvar uu____8366) ->
              let uu____8367 =
                let uu____8368 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8369 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8368 uu____8369
                 in
              failwith uu____8367
          | (uu____8370,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8371 =
                let uu____8372 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8373 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8372 uu____8373
                 in
              failwith uu____8371
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8397 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8397
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8411 = occurs_univ v1 u3  in
              if uu____8411
              then
                let uu____8412 =
                  let uu____8413 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8414 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8413 uu____8414
                   in
                try_umax_components u11 u21 uu____8412
              else
                (let uu____8416 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8416)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8428 = occurs_univ v1 u3  in
              if uu____8428
              then
                let uu____8429 =
                  let uu____8430 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8431 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8430 uu____8431
                   in
                try_umax_components u11 u21 uu____8429
              else
                (let uu____8433 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8433)
          | (FStar_Syntax_Syntax.U_max uu____8434,uu____8435) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8441 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8441
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8443,FStar_Syntax_Syntax.U_max uu____8444) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8450 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8450
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8452,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8453,FStar_Syntax_Syntax.U_name
             uu____8454) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8455) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8456) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8457,FStar_Syntax_Syntax.U_succ
             uu____8458) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8459,FStar_Syntax_Syntax.U_zero
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
      let uu____8559 = bc1  in
      match uu____8559 with
      | (bs1,mk_cod1) ->
          let uu____8603 = bc2  in
          (match uu____8603 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____8714 = aux xs ys  in
                     (match uu____8714 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____8797 =
                       let uu____8804 = mk_cod1 xs  in ([], uu____8804)  in
                     let uu____8807 =
                       let uu____8814 = mk_cod2 ys  in ([], uu____8814)  in
                     (uu____8797, uu____8807)
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
                  let uu____8882 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____8882 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____8885 =
                    let uu____8886 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____8886 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____8885
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____8891 = has_type_guard t1 t2  in (uu____8891, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____8892 = has_type_guard t2 t1  in (uu____8892, wl)
  
let is_flex_pat :
  'Auu____8901 'Auu____8902 'Auu____8903 .
    ('Auu____8901,'Auu____8902,'Auu____8903 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___329_8916  ->
    match uu___329_8916 with
    | (uu____8925,uu____8926,[]) -> true
    | uu____8929 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8960 = f  in
      match uu____8960 with
      | (uu____8967,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8968;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8969;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8972;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8973;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8974;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9026  ->
                 match uu____9026 with
                 | (y,uu____9032) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9154 =
                  let uu____9167 =
                    let uu____9170 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9170  in
                  ((FStar_List.rev pat_binders), uu____9167)  in
                FStar_Pervasives_Native.Some uu____9154
            | (uu____9197,[]) ->
                let uu____9220 =
                  let uu____9233 =
                    let uu____9236 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9236  in
                  ((FStar_List.rev pat_binders), uu____9233)  in
                FStar_Pervasives_Native.Some uu____9220
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9301 =
                  let uu____9302 = FStar_Syntax_Subst.compress a  in
                  uu____9302.FStar_Syntax_Syntax.n  in
                (match uu____9301 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9320 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9320
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___354_9341 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___354_9341.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___354_9341.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9345 =
                            let uu____9346 =
                              let uu____9353 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9353)  in
                            FStar_Syntax_Syntax.NT uu____9346  in
                          [uu____9345]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___355_9365 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___355_9365.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___355_9365.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9366 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9394 =
                  let uu____9407 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9407  in
                (match uu____9394 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9470 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9497 ->
               let uu____9498 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9498 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9774 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____9774
       then
         let uu____9775 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9775
       else ());
      (let uu____9777 = next_prob probs  in
       match uu____9777 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___356_9804 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___356_9804.wl_deferred);
               ctr = (uu___356_9804.ctr);
               defer_ok = (uu___356_9804.defer_ok);
               smt_ok = (uu___356_9804.smt_ok);
               tcenv = (uu___356_9804.tcenv);
               wl_implicits = (uu___356_9804.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____9812 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____9812
                 then
                   let uu____9813 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____9813
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
                           (let uu___357_9818 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___357_9818.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___357_9818.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___357_9818.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___357_9818.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___357_9818.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___357_9818.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___357_9818.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___357_9818.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___357_9818.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9840 ->
                let uu____9849 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9908  ->
                          match uu____9908 with
                          | (c,uu____9916,uu____9917) -> c < probs.ctr))
                   in
                (match uu____9849 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9958 =
                            let uu____9963 =
                              FStar_List.map
                                (fun uu____9978  ->
                                   match uu____9978 with
                                   | (uu____9989,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9963, (probs.wl_implicits))  in
                          Success uu____9958
                      | uu____9992 ->
                          let uu____10001 =
                            let uu___358_10002 = probs  in
                            let uu____10003 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10022  ->
                                      match uu____10022 with
                                      | (uu____10029,uu____10030,y) -> y))
                               in
                            {
                              attempting = uu____10003;
                              wl_deferred = rest;
                              ctr = (uu___358_10002.ctr);
                              defer_ok = (uu___358_10002.defer_ok);
                              smt_ok = (uu___358_10002.smt_ok);
                              tcenv = (uu___358_10002.tcenv);
                              wl_implicits = (uu___358_10002.wl_implicits)
                            }  in
                          solve env uu____10001))))

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
            let uu____10037 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10037 with
            | USolved wl1 ->
                let uu____10039 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10039
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
                  let uu____10091 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10091 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10094 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10106;
                  FStar_Syntax_Syntax.vars = uu____10107;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10110;
                  FStar_Syntax_Syntax.vars = uu____10111;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10123,uu____10124) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10131,FStar_Syntax_Syntax.Tm_uinst uu____10132) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10139 -> USolved wl

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
            ((let uu____10149 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10149
              then
                let uu____10150 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10150 msg
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
               let uu____10236 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10236 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10289 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10289
                then
                  let uu____10290 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10291 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10290 uu____10291
                else ());
               (let uu____10293 = head_matches_delta env1 () t1 t2  in
                match uu____10293 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10338 = eq_prob t1 t2 wl2  in
                         (match uu____10338 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____10359 ->
                         let uu____10368 = eq_prob t1 t2 wl2  in
                         (match uu____10368 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____10417 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____10432 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____10433 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____10432, uu____10433)
                           | FStar_Pervasives_Native.None  ->
                               let uu____10438 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____10439 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____10438, uu____10439)
                            in
                         (match uu____10417 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____10470 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____10470 with
                                | (t1_hd,t1_args) ->
                                    let uu____10509 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____10509 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____10563 =
                                              let uu____10570 =
                                                let uu____10579 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____10579 :: t1_args  in
                                              let uu____10592 =
                                                let uu____10599 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____10599 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____10640  ->
                                                   fun uu____10641  ->
                                                     fun uu____10642  ->
                                                       match (uu____10640,
                                                               uu____10641,
                                                               uu____10642)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____10684),
                                                          (a2,uu____10686))
                                                           ->
                                                           let uu____10711 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____10711
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____10570
                                                uu____10592
                                               in
                                            match uu____10563 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___359_10737 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___359_10737.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___359_10737.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____10753 =
                                                  solve env1 wl'  in
                                                (match uu____10753 with
                                                 | Success (uu____10756,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___360_10760
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___360_10760.attempting);
                                                            wl_deferred =
                                                              (uu___360_10760.wl_deferred);
                                                            ctr =
                                                              (uu___360_10760.ctr);
                                                            defer_ok =
                                                              (uu___360_10760.defer_ok);
                                                            smt_ok =
                                                              (uu___360_10760.smt_ok);
                                                            tcenv =
                                                              (uu___360_10760.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____10769 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____10801 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____10801 with
                                | (t1_base,p1_opt) ->
                                    let uu____10848 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____10848 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____10958 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____10958
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
                                               let uu____11006 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11006
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
                                               let uu____11036 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11036
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
                                               let uu____11066 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11066
                                           | uu____11069 -> t_base  in
                                         let uu____11086 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11086 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11100 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11100, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11107 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11107 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11154 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11154 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11201 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11201
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
                              let uu____11225 = combine t11 t21 wl2  in
                              (match uu____11225 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11258 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11258
                                     then
                                       let uu____11259 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11259
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11298 ts1 =
               match uu____11298 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____11361 = pairwise out t wl2  in
                        (match uu____11361 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____11397 =
               let uu____11408 = FStar_List.hd ts  in (uu____11408, [], wl1)
                in
             let uu____11417 = FStar_List.tl ts  in
             aux uu____11397 uu____11417  in
           let uu____11424 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____11424 with
           | (this_flex,this_rigid) ->
               let uu____11448 =
                 let uu____11449 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____11449.FStar_Syntax_Syntax.n  in
               (match uu____11448 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____11470 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____11470
                    then
                      let uu____11471 = destruct_flex_t this_flex wl  in
                      (match uu____11471 with
                       | (flex,wl1) ->
                           let uu____11478 = quasi_pattern env flex  in
                           (match uu____11478 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____11496 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____11496
                                  then
                                    let uu____11497 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____11497
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____11500 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___361_11503 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___361_11503.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___361_11503.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___361_11503.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___361_11503.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___361_11503.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___361_11503.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___361_11503.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___361_11503.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___361_11503.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____11500)
                | uu____11504 ->
                    ((let uu____11506 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11506
                      then
                        let uu____11507 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____11507
                      else ());
                     (let uu____11509 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____11509 with
                      | (u,_args) ->
                          let uu____11546 =
                            let uu____11547 = FStar_Syntax_Subst.compress u
                               in
                            uu____11547.FStar_Syntax_Syntax.n  in
                          (match uu____11546 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____11574 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____11574 with
                                 | (u',uu____11590) ->
                                     let uu____11611 =
                                       let uu____11612 = whnf env u'  in
                                       uu____11612.FStar_Syntax_Syntax.n  in
                                     (match uu____11611 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____11633 -> false)
                                  in
                               let uu____11634 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___330_11657  ->
                                         match uu___330_11657 with
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
                                              | uu____11666 -> false)
                                         | uu____11669 -> false))
                                  in
                               (match uu____11634 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____11683 = whnf env this_rigid
                                         in
                                      let uu____11684 =
                                        FStar_List.collect
                                          (fun uu___331_11690  ->
                                             match uu___331_11690 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____11696 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____11696]
                                             | uu____11698 -> [])
                                          bounds_probs
                                         in
                                      uu____11683 :: uu____11684  in
                                    let uu____11699 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____11699 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____11730 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____11745 =
                                               let uu____11746 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____11746.FStar_Syntax_Syntax.n
                                                in
                                             match uu____11745 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____11758 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____11758)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____11767 -> bound  in
                                           let uu____11768 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____11768)  in
                                         (match uu____11730 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____11797 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____11797
                                                then
                                                  let wl'1 =
                                                    let uu___362_11799 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___362_11799.wl_deferred);
                                                      ctr =
                                                        (uu___362_11799.ctr);
                                                      defer_ok =
                                                        (uu___362_11799.defer_ok);
                                                      smt_ok =
                                                        (uu___362_11799.smt_ok);
                                                      tcenv =
                                                        (uu___362_11799.tcenv);
                                                      wl_implicits =
                                                        (uu___362_11799.wl_implicits)
                                                    }  in
                                                  let uu____11800 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____11800
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11803 =
                                                  solve_t env eq_prob
                                                    (let uu___363_11805 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___363_11805.wl_deferred);
                                                       ctr =
                                                         (uu___363_11805.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___363_11805.smt_ok);
                                                       tcenv =
                                                         (uu___363_11805.tcenv);
                                                       wl_implicits =
                                                         (uu___363_11805.wl_implicits)
                                                     })
                                                   in
                                                match uu____11803 with
                                                | Success uu____11806 ->
                                                    let wl2 =
                                                      let uu___364_11812 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___364_11812.wl_deferred);
                                                        ctr =
                                                          (uu___364_11812.ctr);
                                                        defer_ok =
                                                          (uu___364_11812.defer_ok);
                                                        smt_ok =
                                                          (uu___364_11812.smt_ok);
                                                        tcenv =
                                                          (uu___364_11812.tcenv);
                                                        wl_implicits =
                                                          (uu___364_11812.wl_implicits)
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
                                                    let uu____11827 =
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
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     (let uu____11839 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____11839
                                                      then
                                                        let uu____11840 =
                                                          let uu____11841 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____11841
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____11840
                                                      else ());
                                                     (let uu____11847 =
                                                        let uu____11862 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____11862)
                                                         in
                                                      match uu____11847 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____11884))
                                                          ->
                                                          let uu____11909 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____11909
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
                                                                 let uu____11926
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____11926)))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          let uu____11950 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____11950
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
                                                                    phi
                                                                    in
                                                                 let wl3 =
                                                                   let uu____11968
                                                                    =
                                                                    let uu____11973
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11973
                                                                     in
                                                                   solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____11968
                                                                    [] wl2
                                                                    in
                                                                 let uu____11978
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____11978)))
                                                      | uu____11979 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____11994 when flip ->
                               let uu____11995 =
                                 let uu____11996 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____11997 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____11996 uu____11997
                                  in
                               failwith uu____11995
                           | uu____11998 ->
                               let uu____11999 =
                                 let uu____12000 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12001 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12000 uu____12001
                                  in
                               failwith uu____11999)))))

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
                      (fun uu____12029  ->
                         match uu____12029 with
                         | (x,i) ->
                             let uu____12040 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12040, i)) bs_lhs
                     in
                  let uu____12041 = lhs  in
                  match uu____12041 with
                  | (uu____12042,u_lhs,uu____12044) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12137 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12147 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12147, univ)
                             in
                          match uu____12137 with
                          | (k,univ) ->
                              let uu____12154 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12154 with
                               | (uu____12169,u,wl3) ->
                                   let uu____12172 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12172, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12198 =
                              let uu____12209 =
                                let uu____12218 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12218 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12261  ->
                                   fun uu____12262  ->
                                     match (uu____12261, uu____12262) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12341 =
                                           let uu____12348 =
                                             let uu____12351 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12351
                                              in
                                           copy_uvar u_lhs [] uu____12348 wl2
                                            in
                                         (match uu____12341 with
                                          | (uu____12376,t_a,wl3) ->
                                              let uu____12379 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____12379 with
                                               | (uu____12396,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12209
                                ([], wl1)
                               in
                            (match uu____12198 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___365_12438 = ct  in
                                   let uu____12439 =
                                     let uu____12442 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12442
                                      in
                                   let uu____12451 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___365_12438.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___365_12438.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12439;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12451;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___365_12438.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___366_12465 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___366_12465.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___366_12465.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12468 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12468 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12522 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12522 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12533 =
                                          let uu____12538 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12538)  in
                                        TERM uu____12533  in
                                      let uu____12539 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12539 with
                                       | (sub_prob,wl3) ->
                                           let uu____12550 =
                                             let uu____12551 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12551
                                              in
                                           solve env uu____12550))
                             | (x,imp)::formals2 ->
                                 let uu____12565 =
                                   let uu____12572 =
                                     let uu____12575 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____12575
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____12572 wl1
                                    in
                                 (match uu____12565 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____12594 =
                                          let uu____12597 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12597
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12594 u_x
                                         in
                                      let uu____12598 =
                                        let uu____12601 =
                                          let uu____12604 =
                                            let uu____12605 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12605, imp)  in
                                          [uu____12604]  in
                                        FStar_List.append bs_terms
                                          uu____12601
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12598 formals2 wl2)
                              in
                           let uu____12622 = occurs_check u_lhs arrow1  in
                           (match uu____12622 with
                            | (uu____12633,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____12644 =
                                    let uu____12645 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____12645
                                     in
                                  giveup_or_defer env orig wl uu____12644
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
              (let uu____12672 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12672
               then
                 let uu____12673 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12674 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12673 (rel_to_string (p_rel orig)) uu____12674
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____12779 = rhs wl1 scope env1 subst1  in
                     (match uu____12779 with
                      | (rhs_prob,wl2) ->
                          ((let uu____12799 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____12799
                            then
                              let uu____12800 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____12800
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___367_12854 = hd1  in
                       let uu____12855 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___367_12854.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___367_12854.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12855
                       }  in
                     let hd21 =
                       let uu___368_12859 = hd2  in
                       let uu____12860 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___368_12859.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___368_12859.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12860
                       }  in
                     let uu____12863 =
                       let uu____12868 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____12868
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____12863 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____12887 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____12887
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____12891 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____12891 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____12946 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____12946
                                  in
                               ((let uu____12958 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____12958
                                 then
                                   let uu____12959 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____12960 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____12959
                                     uu____12960
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____12987 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13016 = aux wl [] env [] bs1 bs2  in
               match uu____13016 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13063 = attempt sub_probs wl2  in
                   solve env uu____13063)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13068 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13068 wl)

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
              let uu____13082 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13082 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13112 = lhs1  in
              match uu____13112 with
              | (uu____13115,ctx_u,uu____13117) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13123 ->
                        let uu____13124 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13124 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13171 = quasi_pattern env1 lhs1  in
              match uu____13171 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13201) ->
                  let uu____13206 = lhs1  in
                  (match uu____13206 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13220 = occurs_check ctx_u rhs1  in
                       (match uu____13220 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13262 =
                                let uu____13269 =
                                  let uu____13270 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13270
                                   in
                                FStar_Util.Inl uu____13269  in
                              (uu____13262, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13290 =
                                 let uu____13291 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13291  in
                               if uu____13290
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13311 =
                                    let uu____13318 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13318  in
                                  let uu____13323 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13311, uu____13323)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13385  ->
                     match uu____13385 with
                     | (x,i) ->
                         let uu____13396 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13396, i)) bs_lhs
                 in
              let uu____13397 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13397 with
              | (rhs_hd,args) ->
                  let uu____13434 = FStar_Util.prefix args  in
                  (match uu____13434 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13492 = lhs1  in
                       (match uu____13492 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13496 =
                              let uu____13507 =
                                let uu____13514 =
                                  let uu____13517 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13517
                                   in
                                copy_uvar u_lhs [] uu____13514 wl1  in
                              match uu____13507 with
                              | (uu____13542,t_last_arg,wl2) ->
                                  let uu____13545 =
                                    let uu____13552 =
                                      let uu____13553 =
                                        let uu____13560 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____13560]  in
                                      FStar_List.append bs_lhs uu____13553
                                       in
                                    copy_uvar u_lhs uu____13552 t_res_lhs wl2
                                     in
                                  (match uu____13545 with
                                   | (uu____13587,lhs',wl3) ->
                                       let uu____13590 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____13590 with
                                        | (uu____13607,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13496 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13628 =
                                     let uu____13629 =
                                       let uu____13634 =
                                         let uu____13635 =
                                           let uu____13638 =
                                             let uu____13643 =
                                               let uu____13644 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13644]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13643
                                              in
                                           uu____13638
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13635
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13634)  in
                                     TERM uu____13629  in
                                   [uu____13628]  in
                                 let uu____13665 =
                                   let uu____13672 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____13672 with
                                   | (p1,wl3) ->
                                       let uu____13689 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____13689 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13665 with
                                  | (sub_probs,wl3) ->
                                      let uu____13716 =
                                        let uu____13717 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____13717  in
                                      solve env1 uu____13716))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____13750 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____13750 with
                | (uu____13765,args) ->
                    (match args with | [] -> false | uu____13793 -> true)
                 in
              let is_arrow rhs2 =
                let uu____13808 =
                  let uu____13809 = FStar_Syntax_Subst.compress rhs2  in
                  uu____13809.FStar_Syntax_Syntax.n  in
                match uu____13808 with
                | FStar_Syntax_Syntax.Tm_arrow uu____13812 -> true
                | uu____13825 -> false  in
              let uu____13826 = quasi_pattern env1 lhs1  in
              match uu____13826 with
              | FStar_Pervasives_Native.None  ->
                  let uu____13837 =
                    let uu____13838 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____13838
                     in
                  giveup_or_defer env1 orig1 wl1 uu____13837
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____13845 = is_app rhs1  in
                  if uu____13845
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____13847 = is_arrow rhs1  in
                     if uu____13847
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____13849 =
                          let uu____13850 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____13850
                           in
                        giveup_or_defer env1 orig1 wl1 uu____13849))
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
                let uu____13853 = lhs  in
                (match uu____13853 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____13857 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____13857 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____13872 =
                              let uu____13875 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____13875
                               in
                            FStar_All.pipe_right uu____13872
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____13890 = occurs_check ctx_uv rhs1  in
                          (match uu____13890 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____13912 =
                                   let uu____13913 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____13913
                                    in
                                 giveup_or_defer env orig wl uu____13912
                               else
                                 (let uu____13915 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____13915
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____13920 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____13920
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____13922 =
                                         let uu____13923 =
                                           names_to_string1 fvs2  in
                                         let uu____13924 =
                                           names_to_string1 fvs1  in
                                         let uu____13925 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____13923 uu____13924
                                           uu____13925
                                          in
                                       giveup_or_defer env orig wl
                                         uu____13922)
                                    else first_order orig env wl lhs rhs1))
                      | uu____13931 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____13935 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____13935 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____13958 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____13958
                             | (FStar_Util.Inl msg,uu____13960) ->
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
                  (let uu____13989 =
                     let uu____14006 = quasi_pattern env lhs  in
                     let uu____14013 = quasi_pattern env rhs  in
                     (uu____14006, uu____14013)  in
                   match uu____13989 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14056 = lhs  in
                       (match uu____14056 with
                        | ({ FStar_Syntax_Syntax.n = uu____14057;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14059;_},u_lhs,uu____14061)
                            ->
                            let uu____14064 = rhs  in
                            (match uu____14064 with
                             | (uu____14065,u_rhs,uu____14067) ->
                                 let uu____14068 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14068
                                 then
                                   let uu____14069 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14069
                                 else
                                   (let uu____14071 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14071 with
                                    | (sub_prob,wl1) ->
                                        let uu____14082 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14082 with
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
                                             let uu____14110 =
                                               let uu____14117 =
                                                 let uu____14120 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14120
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
                                                 uu____14117
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14110 with
                                              | (uu____14123,w,wl2) ->
                                                  let w_app =
                                                    let uu____14129 =
                                                      let uu____14134 =
                                                        FStar_List.map
                                                          (fun uu____14143 
                                                             ->
                                                             match uu____14143
                                                             with
                                                             | (z,uu____14149)
                                                                 ->
                                                                 let uu____14150
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14150)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14134
                                                       in
                                                    uu____14129
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14154 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14154
                                                    then
                                                      let uu____14155 =
                                                        let uu____14158 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14159 =
                                                          let uu____14162 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14163 =
                                                            let uu____14166 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14167 =
                                                              let uu____14170
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14175
                                                                =
                                                                let uu____14178
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14183
                                                                  =
                                                                  let uu____14186
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14186]
                                                                   in
                                                                uu____14178
                                                                  ::
                                                                  uu____14183
                                                                 in
                                                              uu____14170 ::
                                                                uu____14175
                                                               in
                                                            uu____14166 ::
                                                              uu____14167
                                                             in
                                                          uu____14162 ::
                                                            uu____14163
                                                           in
                                                        uu____14158 ::
                                                          uu____14159
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14155
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14192 =
                                                          let uu____14197 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14197)
                                                           in
                                                        TERM uu____14192  in
                                                      let uu____14198 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14198
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14203 =
                                                             let uu____14208
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
                                                               uu____14208)
                                                              in
                                                           TERM uu____14203
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14209 =
                                                      let uu____14210 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14210
                                                       in
                                                    solve env uu____14209)))))))
                   | uu____14211 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14275 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14275
            then
              let uu____14276 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14277 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14278 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14279 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14276 uu____14277 uu____14278 uu____14279
            else ());
           (let uu____14283 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14283
            then
              let uu____14284 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14285 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14286 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14287 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14284 uu____14285 uu____14286 uu____14287
            else ());
           (let uu____14289 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14289 with
            | (head1,args1) ->
                let uu____14326 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14326 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____14380 =
                         let uu____14381 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14382 = args_to_string args1  in
                         let uu____14383 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____14384 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____14381 uu____14382 uu____14383 uu____14384
                          in
                       giveup env1 uu____14380 orig
                     else
                       (let uu____14386 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____14392 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____14392 = FStar_Syntax_Util.Equal)
                           in
                        if uu____14386
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___369_14394 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___369_14394.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___369_14394.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___369_14394.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___369_14394.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___369_14394.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___369_14394.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___369_14394.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___369_14394.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             (let uu____14396 =
                                solve_maybe_uinsts env1 orig head1 head2 wl1
                                 in
                              match uu____14396 with
                              | USolved wl2 ->
                                  let uu____14398 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None [] wl2
                                     in
                                  solve env1 uu____14398
                              | UFailed msg -> giveup env1 msg orig
                              | UDeferred wl2 ->
                                  solve env1
                                    (defer "universe constraints" orig wl2)))
                        else
                          (let uu____14402 = base_and_refinement env1 t1  in
                           match uu____14402 with
                           | (base1,refinement1) ->
                               let uu____14427 = base_and_refinement env1 t2
                                  in
                               (match uu____14427 with
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
                                           let uu____14531 =
                                             FStar_List.fold_right
                                               (fun uu____14567  ->
                                                  fun uu____14568  ->
                                                    match (uu____14567,
                                                            uu____14568)
                                                    with
                                                    | (((a1,uu____14612),
                                                        (a2,uu____14614)),
                                                       (probs,wl2)) ->
                                                        let uu____14647 =
                                                          let uu____14654 =
                                                            p_scope orig  in
                                                          mk_problem wl2
                                                            uu____14654 orig
                                                            a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____14647
                                                         with
                                                         | (prob',wl3) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl3)))
                                               argp ([], wl1)
                                              in
                                           (match uu____14531 with
                                            | (subprobs,wl2) ->
                                                ((let uu____14684 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "Rel")
                                                     in
                                                  if uu____14684
                                                  then
                                                    let uu____14685 =
                                                      FStar_Syntax_Print.list_to_string
                                                        (prob_to_string env1)
                                                        subprobs
                                                       in
                                                    FStar_Util.print1
                                                      "Adding subproblems for arguments: %s"
                                                      uu____14685
                                                  else ());
                                                 (let formula =
                                                    let uu____14690 =
                                                      FStar_List.map
                                                        (fun p  -> p_guard p)
                                                        subprobs
                                                       in
                                                    FStar_Syntax_Util.mk_conj_l
                                                      uu____14690
                                                     in
                                                  let wl3 =
                                                    solve_prob orig
                                                      (FStar_Pervasives_Native.Some
                                                         formula) [] wl2
                                                     in
                                                  let uu____14698 =
                                                    attempt subprobs wl3  in
                                                  solve env1 uu____14698)))
                                         else
                                           (let uu____14700 =
                                              solve_maybe_uinsts env1 orig
                                                head1 head2 wl1
                                               in
                                            match uu____14700 with
                                            | UFailed msg ->
                                                giveup env1 msg orig
                                            | UDeferred wl2 ->
                                                solve env1
                                                  (defer
                                                     "universe constraints"
                                                     orig wl2)
                                            | USolved wl2 ->
                                                let uu____14704 =
                                                  FStar_List.fold_right2
                                                    (fun uu____14737  ->
                                                       fun uu____14738  ->
                                                         fun uu____14739  ->
                                                           match (uu____14737,
                                                                   uu____14738,
                                                                   uu____14739)
                                                           with
                                                           | ((a,uu____14775),
                                                              (a',uu____14777),
                                                              (subprobs,wl3))
                                                               ->
                                                               let uu____14798
                                                                 =
                                                                 mk_t_problem
                                                                   wl3 []
                                                                   orig a
                                                                   FStar_TypeChecker_Common.EQ
                                                                   a'
                                                                   FStar_Pervasives_Native.None
                                                                   "index"
                                                                  in
                                                               (match uu____14798
                                                                with
                                                                | (p,wl4) ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                    args1 args2 ([], wl2)
                                                   in
                                                (match uu____14704 with
                                                 | (subprobs,wl3) ->
                                                     ((let uu____14826 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           (FStar_Options.Other
                                                              "Rel")
                                                          in
                                                       if uu____14826
                                                       then
                                                         let uu____14827 =
                                                           FStar_Syntax_Print.list_to_string
                                                             (prob_to_string
                                                                env1)
                                                             subprobs
                                                            in
                                                         FStar_Util.print1
                                                           "Adding subproblems for arguments: %s\n"
                                                           uu____14827
                                                       else ());
                                                      FStar_List.iter
                                                        (def_check_prob
                                                           "solve_t' subprobs")
                                                        subprobs;
                                                      (let formula =
                                                         let uu____14833 =
                                                           FStar_List.map
                                                             p_guard subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____14833
                                                          in
                                                       let wl4 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl3
                                                          in
                                                       let uu____14841 =
                                                         attempt subprobs wl4
                                                          in
                                                       solve env1 uu____14841))))
                                     | uu____14842 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___370_14882 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___370_14882.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___370_14882.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___370_14882.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___370_14882.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___370_14882.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___370_14882.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___370_14882.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___370_14882.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____14957 = destruct_flex_t scrutinee wl1  in
             match uu____14957 with
             | ((_t,uv,_args),wl2) ->
                 let tc_annot env2 t =
                   let uu____14983 =
                     env2.FStar_TypeChecker_Env.type_of env2 t  in
                   match uu____14983 with | (t1,uu____14995,g) -> (t1, g)  in
                 let uu____14997 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p
                     tc_annot
                    in
                 (match uu____14997 with
                  | (xs,pat_term,uu____15012,uu____15013) ->
                      let uu____15018 =
                        FStar_List.fold_left
                          (fun uu____15041  ->
                             fun x  ->
                               match uu____15041 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____15062 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____15062 with
                                    | (uu____15079,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____15018 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____15100 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____15100 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___371_15116 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___371_15116.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    tcenv = (uu___371_15116.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____15132 = solve env1 wl'  in
                                (match uu____15132 with
                                 | Success (uu____15135,imps) ->
                                     let wl'1 =
                                       let uu___372_15138 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___372_15138.wl_deferred);
                                         ctr = (uu___372_15138.ctr);
                                         defer_ok = (uu___372_15138.defer_ok);
                                         smt_ok = (uu___372_15138.smt_ok);
                                         tcenv = (uu___372_15138.tcenv);
                                         wl_implicits =
                                           (uu___372_15138.wl_implicits)
                                       }  in
                                     let uu____15139 = solve env1 wl'1  in
                                     (match uu____15139 with
                                      | Success (uu____15142,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___373_15146 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___373_15146.attempting);
                                                 wl_deferred =
                                                   (uu___373_15146.wl_deferred);
                                                 ctr = (uu___373_15146.ctr);
                                                 defer_ok =
                                                   (uu___373_15146.defer_ok);
                                                 smt_ok =
                                                   (uu___373_15146.smt_ok);
                                                 tcenv =
                                                   (uu___373_15146.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____15163 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____15169 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____15190 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____15190
                 then
                   let uu____15191 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____15192 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____15191 uu____15192
                 else ());
                (let uu____15194 =
                   let uu____15215 =
                     let uu____15224 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____15224)  in
                   let uu____15231 =
                     let uu____15240 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____15240)  in
                   (uu____15215, uu____15231)  in
                 match uu____15194 with
                 | ((uu____15269,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____15272;
                                   FStar_Syntax_Syntax.vars = uu____15273;_}),
                    (s,t)) ->
                     let uu____15344 =
                       let uu____15345 = is_flex scrutinee  in
                       Prims.op_Negation uu____15345  in
                     if uu____15344
                     then
                       ((let uu____15353 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____15353
                         then
                           let uu____15354 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____15354
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____15366 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15366
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____15372 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15372
                           then
                             let uu____15373 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____15374 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____15373 uu____15374
                           else ());
                          (let pat_discriminates uu___332_15395 =
                             match uu___332_15395 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____15410;
                                  FStar_Syntax_Syntax.p = uu____15411;_},FStar_Pervasives_Native.None
                                ,uu____15412) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____15425;
                                  FStar_Syntax_Syntax.p = uu____15426;_},FStar_Pervasives_Native.None
                                ,uu____15427) -> true
                             | uu____15452 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____15552 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____15552 with
                                       | (uu____15553,uu____15554,t') ->
                                           let uu____15572 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____15572 with
                                            | (FullMatch ,uu____15583) ->
                                                true
                                            | (HeadMatch
                                               uu____15596,uu____15597) ->
                                                true
                                            | uu____15610 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____15643 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15643
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____15660 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____15660 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____15760,uu____15761) ->
                                       branches1
                                   | uu____15906 -> branches  in
                                 let uu____15961 =
                                   FStar_Util.find_map try_branches
                                     (fun uu____15980  ->
                                        match uu____15980 with
                                        | (p,uu____15996,uu____15997) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____15961))
                           | FStar_Pervasives_Native.Some (p,uu____16021,e)
                               ->
                               ((let uu____16054 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16054
                                 then
                                   let uu____16055 =
                                     FStar_Syntax_Print.pat_to_string p  in
                                   let uu____16056 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   FStar_Util.print2
                                     "Found head matching branch %s -> e\n"
                                     uu____16055 uu____16056
                                 else ());
                                (let uu____16058 =
                                   try_solve_branch scrutinee p  in
                                 FStar_All.pipe_left
                                   (fun _0_24  -> FStar_Util.Inr _0_24)
                                   uu____16058))))
                 | ((s,t),(uu____16073,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____16076;
                                         FStar_Syntax_Syntax.vars =
                                           uu____16077;_}))
                     ->
                     let uu____16146 =
                       let uu____16147 = is_flex scrutinee  in
                       Prims.op_Negation uu____16147  in
                     if uu____16146
                     then
                       ((let uu____16155 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16155
                         then
                           let uu____16156 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16156
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16168 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16168
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16174 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16174
                           then
                             let uu____16175 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16176 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16175 uu____16176
                           else ());
                          (let pat_discriminates uu___332_16197 =
                             match uu___332_16197 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16212;
                                  FStar_Syntax_Syntax.p = uu____16213;_},FStar_Pervasives_Native.None
                                ,uu____16214) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16227;
                                  FStar_Syntax_Syntax.p = uu____16228;_},FStar_Pervasives_Native.None
                                ,uu____16229) -> true
                             | uu____16254 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16354 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16354 with
                                       | (uu____16355,uu____16356,t') ->
                                           let uu____16374 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____16374 with
                                            | (FullMatch ,uu____16385) ->
                                                true
                                            | (HeadMatch
                                               uu____16398,uu____16399) ->
                                                true
                                            | uu____16412 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16445 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16445
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16462 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16462 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16562,uu____16563) ->
                                       branches1
                                   | uu____16708 -> branches  in
                                 let uu____16763 =
                                   FStar_Util.find_map try_branches
                                     (fun uu____16782  ->
                                        match uu____16782 with
                                        | (p,uu____16798,uu____16799) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____16763))
                           | FStar_Pervasives_Native.Some (p,uu____16823,e)
                               ->
                               ((let uu____16856 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16856
                                 then
                                   let uu____16857 =
                                     FStar_Syntax_Print.pat_to_string p  in
                                   let uu____16858 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   FStar_Util.print2
                                     "Found head matching branch %s -> e\n"
                                     uu____16857 uu____16858
                                 else ());
                                (let uu____16860 =
                                   try_solve_branch scrutinee p  in
                                 FStar_All.pipe_left
                                   (fun _0_26  -> FStar_Util.Inr _0_26)
                                   uu____16860))))
                 | uu____16873 ->
                     ((let uu____16895 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____16895
                       then
                         let uu____16896 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____16897 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____16896 uu____16897
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____16938 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____16938
            then
              let uu____16939 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16940 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____16941 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16942 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____16939 uu____16940 uu____16941 uu____16942
            else ());
           (let uu____16944 = head_matches_delta env1 wl1 t1 t2  in
            match uu____16944 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____16975,uu____16976) ->
                     let rec may_relate head3 =
                       let uu____17003 =
                         let uu____17004 = FStar_Syntax_Subst.compress head3
                            in
                         uu____17004.FStar_Syntax_Syntax.n  in
                       match uu____17003 with
                       | FStar_Syntax_Syntax.Tm_name uu____17007 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____17008 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____17031;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____17032;
                             FStar_Syntax_Syntax.fv_qual = uu____17033;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____17036;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____17037;
                             FStar_Syntax_Syntax.fv_qual = uu____17038;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____17042,uu____17043) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____17085) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____17091) ->
                           may_relate t
                       | uu____17096 -> false  in
                     let uu____17097 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____17097 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____17112 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____17112
                          then
                            let uu____17113 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____17113 with
                             | (guard,wl2) ->
                                 let uu____17120 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____17120)
                          else
                            (let uu____17122 =
                               let uu____17123 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____17124 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               FStar_Util.format2 "head mismatch (%s vs %s)"
                                 uu____17123 uu____17124
                                in
                             giveup env1 uu____17122 orig))
                 | (HeadMatch (true ),uu____17125) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____17138 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____17138 with
                        | (guard,wl2) ->
                            let uu____17145 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____17145)
                     else
                       (let uu____17147 =
                          let uu____17148 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____17149 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____17148 uu____17149
                           in
                        giveup env1 uu____17147 orig)
                 | (uu____17150,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___374_17164 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___374_17164.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___374_17164.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___374_17164.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___374_17164.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___374_17164.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___374_17164.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___374_17164.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___374_17164.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____17188 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____17188
          then
            let uu____17189 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____17189
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____17194 =
                let uu____17197 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____17197  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____17194 t1);
             (let uu____17209 =
                let uu____17212 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____17212  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____17209 t2);
             (let uu____17224 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____17224
              then
                let uu____17225 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____17226 =
                  let uu____17227 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____17228 =
                    let uu____17229 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____17229  in
                  Prims.strcat uu____17227 uu____17228  in
                let uu____17230 =
                  let uu____17231 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____17232 =
                    let uu____17233 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____17233  in
                  Prims.strcat uu____17231 uu____17232  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____17225
                  uu____17226 uu____17230
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____17236,uu____17237) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____17260,FStar_Syntax_Syntax.Tm_delayed uu____17261) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____17284,uu____17285) ->
                  let uu____17312 =
                    let uu___375_17313 = problem  in
                    let uu____17314 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___375_17313.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____17314;
                      FStar_TypeChecker_Common.relation =
                        (uu___375_17313.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___375_17313.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___375_17313.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___375_17313.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___375_17313.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___375_17313.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___375_17313.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___375_17313.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17312 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____17315,uu____17316) ->
                  let uu____17323 =
                    let uu___376_17324 = problem  in
                    let uu____17325 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___376_17324.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____17325;
                      FStar_TypeChecker_Common.relation =
                        (uu___376_17324.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___376_17324.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___376_17324.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___376_17324.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___376_17324.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___376_17324.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___376_17324.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___376_17324.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17323 wl
              | (uu____17326,FStar_Syntax_Syntax.Tm_ascribed uu____17327) ->
                  let uu____17354 =
                    let uu___377_17355 = problem  in
                    let uu____17356 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___377_17355.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___377_17355.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___377_17355.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____17356;
                      FStar_TypeChecker_Common.element =
                        (uu___377_17355.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___377_17355.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___377_17355.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___377_17355.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___377_17355.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___377_17355.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17354 wl
              | (uu____17357,FStar_Syntax_Syntax.Tm_meta uu____17358) ->
                  let uu____17365 =
                    let uu___378_17366 = problem  in
                    let uu____17367 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___378_17366.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___378_17366.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___378_17366.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____17367;
                      FStar_TypeChecker_Common.element =
                        (uu___378_17366.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___378_17366.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___378_17366.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___378_17366.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___378_17366.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___378_17366.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____17365 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____17369),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____17371)) ->
                  let uu____17380 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____17380
              | (FStar_Syntax_Syntax.Tm_bvar uu____17381,uu____17382) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____17383,FStar_Syntax_Syntax.Tm_bvar uu____17384) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___333_17443 =
                    match uu___333_17443 with
                    | [] -> c
                    | bs ->
                        let uu____17465 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____17465
                     in
                  let uu____17474 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____17474 with
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
                                    let uu____17597 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____17597
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
                  let mk_t t l uu___334_17672 =
                    match uu___334_17672 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____17706 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____17706 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____17825 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____17826 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____17825
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____17826 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____17827,uu____17828) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____17855 -> true
                    | uu____17872 -> false  in
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
                      (let uu____17925 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___379_17933 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___379_17933.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___379_17933.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___379_17933.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___379_17933.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___379_17933.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___379_17933.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___379_17933.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___379_17933.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___379_17933.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___379_17933.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___379_17933.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___379_17933.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___379_17933.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___379_17933.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___379_17933.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___379_17933.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___379_17933.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___379_17933.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___379_17933.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___379_17933.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___379_17933.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___379_17933.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___379_17933.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___379_17933.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___379_17933.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___379_17933.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___379_17933.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___379_17933.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___379_17933.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___379_17933.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___379_17933.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___379_17933.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___379_17933.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___379_17933.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___379_17933.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___379_17933.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___379_17933.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____17925 with
                       | (uu____17936,ty,uu____17938) ->
                           let uu____17939 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____17939)
                     in
                  let uu____17940 =
                    let uu____17957 = maybe_eta t1  in
                    let uu____17964 = maybe_eta t2  in
                    (uu____17957, uu____17964)  in
                  (match uu____17940 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___380_18006 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___380_18006.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___380_18006.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___380_18006.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___380_18006.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___380_18006.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___380_18006.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___380_18006.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___380_18006.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____18027 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18027
                       then
                         let uu____18028 = destruct_flex_t not_abs wl  in
                         (match uu____18028 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___381_18043 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___381_18043.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___381_18043.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___381_18043.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___381_18043.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___381_18043.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___381_18043.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___381_18043.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___381_18043.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____18065 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18065
                       then
                         let uu____18066 = destruct_flex_t not_abs wl  in
                         (match uu____18066 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___381_18081 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___381_18081.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___381_18081.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___381_18081.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___381_18081.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___381_18081.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___381_18081.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___381_18081.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___381_18081.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____18083 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____18100,FStar_Syntax_Syntax.Tm_abs uu____18101) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____18128 -> true
                    | uu____18145 -> false  in
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
                      (let uu____18198 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___379_18206 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___379_18206.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___379_18206.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___379_18206.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___379_18206.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___379_18206.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___379_18206.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___379_18206.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___379_18206.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___379_18206.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___379_18206.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___379_18206.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___379_18206.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___379_18206.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___379_18206.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___379_18206.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___379_18206.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___379_18206.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___379_18206.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___379_18206.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___379_18206.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___379_18206.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___379_18206.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___379_18206.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___379_18206.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___379_18206.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___379_18206.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___379_18206.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___379_18206.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___379_18206.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___379_18206.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___379_18206.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___379_18206.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___379_18206.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___379_18206.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___379_18206.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___379_18206.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___379_18206.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____18198 with
                       | (uu____18209,ty,uu____18211) ->
                           let uu____18212 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____18212)
                     in
                  let uu____18213 =
                    let uu____18230 = maybe_eta t1  in
                    let uu____18237 = maybe_eta t2  in
                    (uu____18230, uu____18237)  in
                  (match uu____18213 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___380_18279 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___380_18279.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___380_18279.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___380_18279.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___380_18279.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___380_18279.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___380_18279.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___380_18279.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___380_18279.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____18300 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18300
                       then
                         let uu____18301 = destruct_flex_t not_abs wl  in
                         (match uu____18301 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___381_18316 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___381_18316.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___381_18316.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___381_18316.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___381_18316.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___381_18316.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___381_18316.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___381_18316.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___381_18316.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____18338 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____18338
                       then
                         let uu____18339 = destruct_flex_t not_abs wl  in
                         (match uu____18339 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___381_18354 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___381_18354.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___381_18354.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___381_18354.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___381_18354.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___381_18354.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___381_18354.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___381_18354.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___381_18354.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____18356 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____18388 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____18388) &&
                       (let uu____18392 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____18392))
                      &&
                      (let uu____18399 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____18399 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___335_18411 =
                             match uu___335_18411 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____18412 -> true
                             | uu____18413 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____18414 -> false)
                     in
                  let uu____18415 = as_refinement should_delta env wl t1  in
                  (match uu____18415 with
                   | (x11,phi1) ->
                       let uu____18428 = as_refinement should_delta env wl t2
                          in
                       (match uu____18428 with
                        | (x21,phi21) ->
                            let uu____18441 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____18441 with
                             | (base_prob,wl1) ->
                                 let x12 = FStar_Syntax_Syntax.freshen_bv x11
                                    in
                                 let subst1 =
                                   [FStar_Syntax_Syntax.DB
                                      ((Prims.parse_int "0"), x12)]
                                    in
                                 let phi11 =
                                   FStar_Syntax_Subst.subst subst1 phi1  in
                                 let phi22 =
                                   FStar_Syntax_Subst.subst subst1 phi21  in
                                 let env1 =
                                   FStar_TypeChecker_Env.push_bv env x12  in
                                 let mk_imp1 imp phi12 phi23 =
                                   let uu____18507 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____18507
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____18519 =
                                   let impl =
                                     if
                                       problem.FStar_TypeChecker_Common.relation
                                         = FStar_TypeChecker_Common.EQ
                                     then
                                       mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                         phi22
                                     else
                                       mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                         phi22
                                      in
                                   let guard =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) impl
                                      in
                                   (let uu____18530 =
                                      let uu____18533 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____18533
                                       in
                                    FStar_TypeChecker_Env.def_check_closed_in
                                      (p_loc orig) "ref.1" uu____18530
                                      (p_guard base_prob));
                                   (let uu____18545 =
                                      let uu____18548 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____18548
                                       in
                                    FStar_TypeChecker_Env.def_check_closed_in
                                      (p_loc orig) "ref.2" uu____18545 impl);
                                   (let wl2 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl1
                                       in
                                    let uu____18560 = attempt [base_prob] wl2
                                       in
                                    solve env1 uu____18560)
                                    in
                                 let has_uvars =
                                   (let uu____18564 =
                                      let uu____18565 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____18565  in
                                    Prims.op_Negation uu____18564) ||
                                     (let uu____18569 =
                                        let uu____18570 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____18570
                                         in
                                      Prims.op_Negation uu____18569)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____18573 =
                                     let uu____18578 =
                                       let uu____18585 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____18585]  in
                                     mk_t_problem wl1 uu____18578 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____18573 with
                                    | (ref_prob,wl2) ->
                                        let uu____18600 =
                                          solve env1
                                            (let uu___382_18602 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___382_18602.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___382_18602.smt_ok);
                                               tcenv = (uu___382_18602.tcenv);
                                               wl_implicits =
                                                 (uu___382_18602.wl_implicits)
                                             })
                                           in
                                        (match uu____18600 with
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
                                         | Success uu____18612 ->
                                             let guard =
                                               let uu____18620 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____18620
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___383_18629 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___383_18629.attempting);
                                                 wl_deferred =
                                                   (uu___383_18629.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___383_18629.defer_ok);
                                                 smt_ok =
                                                   (uu___383_18629.smt_ok);
                                                 tcenv =
                                                   (uu___383_18629.tcenv);
                                                 wl_implicits =
                                                   (uu___383_18629.wl_implicits)
                                               }  in
                                             let uu____18630 =
                                               attempt [base_prob] wl4  in
                                             solve env1 uu____18630))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____18632,FStar_Syntax_Syntax.Tm_uvar uu____18633) ->
                  let uu____18658 = destruct_flex_t t1 wl  in
                  (match uu____18658 with
                   | (f1,wl1) ->
                       let uu____18665 = destruct_flex_t t2 wl1  in
                       (match uu____18665 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18672;
                    FStar_Syntax_Syntax.pos = uu____18673;
                    FStar_Syntax_Syntax.vars = uu____18674;_},uu____18675),FStar_Syntax_Syntax.Tm_uvar
                 uu____18676) ->
                  let uu____18721 = destruct_flex_t t1 wl  in
                  (match uu____18721 with
                   | (f1,wl1) ->
                       let uu____18728 = destruct_flex_t t2 wl1  in
                       (match uu____18728 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____18735,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18736;
                    FStar_Syntax_Syntax.pos = uu____18737;
                    FStar_Syntax_Syntax.vars = uu____18738;_},uu____18739))
                  ->
                  let uu____18784 = destruct_flex_t t1 wl  in
                  (match uu____18784 with
                   | (f1,wl1) ->
                       let uu____18791 = destruct_flex_t t2 wl1  in
                       (match uu____18791 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18798;
                    FStar_Syntax_Syntax.pos = uu____18799;
                    FStar_Syntax_Syntax.vars = uu____18800;_},uu____18801),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18802;
                    FStar_Syntax_Syntax.pos = uu____18803;
                    FStar_Syntax_Syntax.vars = uu____18804;_},uu____18805))
                  ->
                  let uu____18870 = destruct_flex_t t1 wl  in
                  (match uu____18870 with
                   | (f1,wl1) ->
                       let uu____18877 = destruct_flex_t t2 wl1  in
                       (match uu____18877 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____18884,uu____18885) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____18898 = destruct_flex_t t1 wl  in
                  (match uu____18898 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18905;
                    FStar_Syntax_Syntax.pos = uu____18906;
                    FStar_Syntax_Syntax.vars = uu____18907;_},uu____18908),uu____18909)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____18942 = destruct_flex_t t1 wl  in
                  (match uu____18942 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____18949,FStar_Syntax_Syntax.Tm_uvar uu____18950) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____18963,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____18964;
                    FStar_Syntax_Syntax.pos = uu____18965;
                    FStar_Syntax_Syntax.vars = uu____18966;_},uu____18967))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19000,FStar_Syntax_Syntax.Tm_arrow uu____19001) ->
                  solve_t' env
                    (let uu___384_19027 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___384_19027.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___384_19027.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___384_19027.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___384_19027.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___384_19027.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___384_19027.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___384_19027.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___384_19027.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___384_19027.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19028;
                    FStar_Syntax_Syntax.pos = uu____19029;
                    FStar_Syntax_Syntax.vars = uu____19030;_},uu____19031),FStar_Syntax_Syntax.Tm_arrow
                 uu____19032) ->
                  solve_t' env
                    (let uu___384_19078 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___384_19078.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___384_19078.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___384_19078.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___384_19078.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___384_19078.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___384_19078.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___384_19078.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___384_19078.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___384_19078.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____19079,FStar_Syntax_Syntax.Tm_uvar uu____19080) ->
                  let uu____19093 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19093
              | (uu____19094,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19095;
                    FStar_Syntax_Syntax.pos = uu____19096;
                    FStar_Syntax_Syntax.vars = uu____19097;_},uu____19098))
                  ->
                  let uu____19131 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19131
              | (FStar_Syntax_Syntax.Tm_uvar uu____19132,uu____19133) ->
                  let uu____19146 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19146
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19147;
                    FStar_Syntax_Syntax.pos = uu____19148;
                    FStar_Syntax_Syntax.vars = uu____19149;_},uu____19150),uu____19151)
                  ->
                  let uu____19184 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____19184
              | (FStar_Syntax_Syntax.Tm_refine uu____19185,uu____19186) ->
                  let t21 =
                    let uu____19194 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____19194  in
                  solve_t env
                    (let uu___385_19220 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___385_19220.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___385_19220.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___385_19220.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___385_19220.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___385_19220.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___385_19220.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___385_19220.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___385_19220.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___385_19220.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____19221,FStar_Syntax_Syntax.Tm_refine uu____19222) ->
                  let t11 =
                    let uu____19230 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____19230  in
                  solve_t env
                    (let uu___386_19256 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___386_19256.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___386_19256.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___386_19256.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___386_19256.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___386_19256.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___386_19256.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___386_19256.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___386_19256.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___386_19256.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____19338 =
                    let uu____19339 = guard_of_prob env wl problem t1 t2  in
                    match uu____19339 with
                    | (guard,wl1) ->
                        let uu____19346 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____19346
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____19557 = br1  in
                        (match uu____19557 with
                         | (p1,w1,uu____19582) ->
                             let uu____19599 = br2  in
                             (match uu____19599 with
                              | (p2,w2,uu____19618) ->
                                  let uu____19623 =
                                    let uu____19624 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____19624  in
                                  if uu____19623
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____19640 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____19640 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____19673 = br2  in
                                         (match uu____19673 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____19708 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____19708
                                                 in
                                              let uu____19719 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____19742,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____19759) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____19802 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____19802 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____19719
                                                (fun uu____19844  ->
                                                   match uu____19844 with
                                                   | (wprobs,wl2) ->
                                                       let uu____19865 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____19865
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____19880 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____19880
                                                              (fun
                                                                 uu____19904 
                                                                 ->
                                                                 match uu____19904
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____19989 -> FStar_Pervasives_Native.None  in
                  let uu____20026 = solve_branches wl brs1 brs2  in
                  (match uu____20026 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____20054 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____20054 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____20071 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____20071  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____20080 =
                              let uu____20081 =
                                attempt sub_probs1
                                  (let uu___387_20083 = wl3  in
                                   {
                                     attempting = (uu___387_20083.attempting);
                                     wl_deferred =
                                       (uu___387_20083.wl_deferred);
                                     ctr = (uu___387_20083.ctr);
                                     defer_ok = (uu___387_20083.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___387_20083.tcenv);
                                     wl_implicits =
                                       (uu___387_20083.wl_implicits)
                                   })
                                 in
                              solve env uu____20081  in
                            (match uu____20080 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____20087 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____20093,uu____20094) ->
                  let head1 =
                    let uu____20118 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20118
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20158 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20158
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20198 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20198
                    then
                      let uu____20199 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20200 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20201 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20199 uu____20200 uu____20201
                    else ());
                   (let uu____20203 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20203
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20210 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20210
                       then
                         let uu____20211 =
                           let uu____20218 =
                             let uu____20219 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20219 = FStar_Syntax_Util.Equal  in
                           if uu____20218
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20229 = mk_eq2 wl orig t1 t2  in
                              match uu____20229 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20211 with
                         | (guard,wl1) ->
                             let uu____20250 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20250
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____20253,uu____20254) ->
                  let head1 =
                    let uu____20262 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20262
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20302 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20302
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20342 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20342
                    then
                      let uu____20343 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20344 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20345 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20343 uu____20344 uu____20345
                    else ());
                   (let uu____20347 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20347
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20354 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20354
                       then
                         let uu____20355 =
                           let uu____20362 =
                             let uu____20363 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20363 = FStar_Syntax_Util.Equal  in
                           if uu____20362
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20373 = mk_eq2 wl orig t1 t2  in
                              match uu____20373 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20355 with
                         | (guard,wl1) ->
                             let uu____20394 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20394
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____20397,uu____20398) ->
                  let head1 =
                    let uu____20400 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20400
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20440 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20440
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20480 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20480
                    then
                      let uu____20481 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20482 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20483 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20481 uu____20482 uu____20483
                    else ());
                   (let uu____20485 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20485
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20492 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20492
                       then
                         let uu____20493 =
                           let uu____20500 =
                             let uu____20501 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20501 = FStar_Syntax_Util.Equal  in
                           if uu____20500
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20511 = mk_eq2 wl orig t1 t2  in
                              match uu____20511 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20493 with
                         | (guard,wl1) ->
                             let uu____20532 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20532
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____20535,uu____20536) ->
                  let head1 =
                    let uu____20538 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20538
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20578 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20578
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20618 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20618
                    then
                      let uu____20619 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20620 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20621 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20619 uu____20620 uu____20621
                    else ());
                   (let uu____20623 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20623
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20630 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20630
                       then
                         let uu____20631 =
                           let uu____20638 =
                             let uu____20639 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20639 = FStar_Syntax_Util.Equal  in
                           if uu____20638
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20649 = mk_eq2 wl orig t1 t2  in
                              match uu____20649 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20631 with
                         | (guard,wl1) ->
                             let uu____20670 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20670
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____20673,uu____20674) ->
                  let head1 =
                    let uu____20676 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20676
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20716 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20716
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20756 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20756
                    then
                      let uu____20757 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20758 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20759 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20757 uu____20758 uu____20759
                    else ());
                   (let uu____20761 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20761
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20768 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20768
                       then
                         let uu____20769 =
                           let uu____20776 =
                             let uu____20777 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20777 = FStar_Syntax_Util.Equal  in
                           if uu____20776
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20787 = mk_eq2 wl orig t1 t2  in
                              match uu____20787 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20769 with
                         | (guard,wl1) ->
                             let uu____20808 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20808
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____20811,uu____20812) ->
                  let head1 =
                    let uu____20828 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20828
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20868 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20868
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20908 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20908
                    then
                      let uu____20909 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20910 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20911 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20909 uu____20910 uu____20911
                    else ());
                   (let uu____20913 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20913
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20920 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20920
                       then
                         let uu____20921 =
                           let uu____20928 =
                             let uu____20929 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20929 = FStar_Syntax_Util.Equal  in
                           if uu____20928
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20939 = mk_eq2 wl orig t1 t2  in
                              match uu____20939 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20921 with
                         | (guard,wl1) ->
                             let uu____20960 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20960
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____20963,FStar_Syntax_Syntax.Tm_match uu____20964) ->
                  let head1 =
                    let uu____20988 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20988
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21028 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21028
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21068 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21068
                    then
                      let uu____21069 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21070 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21071 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21069 uu____21070 uu____21071
                    else ());
                   (let uu____21073 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____21073
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____21080 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____21080
                       then
                         let uu____21081 =
                           let uu____21088 =
                             let uu____21089 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____21089 = FStar_Syntax_Util.Equal  in
                           if uu____21088
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____21099 = mk_eq2 wl orig t1 t2  in
                              match uu____21099 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____21081 with
                         | (guard,wl1) ->
                             let uu____21120 = solve_prob orig guard [] wl1
                                in
                             solve env uu____21120
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21123,FStar_Syntax_Syntax.Tm_uinst uu____21124) ->
                  let head1 =
                    let uu____21132 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21132
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21172 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21172
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21212 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21212
                    then
                      let uu____21213 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21214 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21215 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21213 uu____21214 uu____21215
                    else ());
                   (let uu____21217 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____21217
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____21224 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____21224
                       then
                         let uu____21225 =
                           let uu____21232 =
                             let uu____21233 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____21233 = FStar_Syntax_Util.Equal  in
                           if uu____21232
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____21243 = mk_eq2 wl orig t1 t2  in
                              match uu____21243 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____21225 with
                         | (guard,wl1) ->
                             let uu____21264 = solve_prob orig guard [] wl1
                                in
                             solve env uu____21264
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21267,FStar_Syntax_Syntax.Tm_name uu____21268) ->
                  let head1 =
                    let uu____21270 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21270
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21310 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21310
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21350 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21350
                    then
                      let uu____21351 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21352 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21353 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21351 uu____21352 uu____21353
                    else ());
                   (let uu____21355 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____21355
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____21362 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____21362
                       then
                         let uu____21363 =
                           let uu____21370 =
                             let uu____21371 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____21371 = FStar_Syntax_Util.Equal  in
                           if uu____21370
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____21381 = mk_eq2 wl orig t1 t2  in
                              match uu____21381 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____21363 with
                         | (guard,wl1) ->
                             let uu____21402 = solve_prob orig guard [] wl1
                                in
                             solve env uu____21402
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21405,FStar_Syntax_Syntax.Tm_constant uu____21406) ->
                  let head1 =
                    let uu____21408 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21408
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21442 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21442
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21476 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21476
                    then
                      let uu____21477 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21478 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21479 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21477 uu____21478 uu____21479
                    else ());
                   (let uu____21481 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____21481
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____21488 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____21488
                       then
                         let uu____21489 =
                           let uu____21496 =
                             let uu____21497 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____21497 = FStar_Syntax_Util.Equal  in
                           if uu____21496
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____21507 = mk_eq2 wl orig t1 t2  in
                              match uu____21507 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____21489 with
                         | (guard,wl1) ->
                             let uu____21528 = solve_prob orig guard [] wl1
                                in
                             solve env uu____21528
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21531,FStar_Syntax_Syntax.Tm_fvar uu____21532) ->
                  let head1 =
                    let uu____21534 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21534
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21568 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21568
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21602 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21602
                    then
                      let uu____21603 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21604 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21605 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21603 uu____21604 uu____21605
                    else ());
                   (let uu____21607 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____21607
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____21614 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____21614
                       then
                         let uu____21615 =
                           let uu____21622 =
                             let uu____21623 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____21623 = FStar_Syntax_Util.Equal  in
                           if uu____21622
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____21633 = mk_eq2 wl orig t1 t2  in
                              match uu____21633 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____21615 with
                         | (guard,wl1) ->
                             let uu____21654 = solve_prob orig guard [] wl1
                                in
                             solve env uu____21654
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____21657,FStar_Syntax_Syntax.Tm_app uu____21658) ->
                  let head1 =
                    let uu____21674 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21674
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21708 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21708
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21748 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21748
                    then
                      let uu____21749 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21750 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21751 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21749 uu____21750 uu____21751
                    else ());
                   (let uu____21753 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____21753
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____21760 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____21760
                       then
                         let uu____21761 =
                           let uu____21768 =
                             let uu____21769 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____21769 = FStar_Syntax_Util.Equal  in
                           if uu____21768
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____21779 = mk_eq2 wl orig t1 t2  in
                              match uu____21779 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____21761 with
                         | (guard,wl1) ->
                             let uu____21800 = solve_prob orig guard [] wl1
                                in
                             solve env uu____21800
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____21803,FStar_Syntax_Syntax.Tm_let uu____21804) ->
                  let uu____21829 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____21829
                  then
                    let uu____21830 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____21830
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____21832,uu____21833) ->
                  let uu____21846 =
                    let uu____21851 =
                      let uu____21852 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____21853 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____21854 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____21855 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____21852 uu____21853 uu____21854 uu____21855
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____21851)
                     in
                  FStar_Errors.raise_error uu____21846
                    t1.FStar_Syntax_Syntax.pos
              | (uu____21856,FStar_Syntax_Syntax.Tm_let uu____21857) ->
                  let uu____21870 =
                    let uu____21875 =
                      let uu____21876 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____21877 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____21878 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____21879 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____21876 uu____21877 uu____21878 uu____21879
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____21875)
                     in
                  FStar_Errors.raise_error uu____21870
                    t1.FStar_Syntax_Syntax.pos
              | uu____21880 -> giveup env "head tag mismatch" orig))))

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
          (let uu____21939 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____21939
           then
             let uu____21940 =
               let uu____21941 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____21941  in
             let uu____21942 =
               let uu____21943 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____21943  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____21940 uu____21942
           else ());
          (let uu____21945 =
             let uu____21946 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____21946  in
           if uu____21945
           then
             let uu____21947 =
               let uu____21948 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____21949 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____21948 uu____21949
                in
             giveup env uu____21947 orig
           else
             (let uu____21951 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____21951 with
              | (ret_sub_prob,wl1) ->
                  let uu____21958 =
                    FStar_List.fold_right2
                      (fun uu____21991  ->
                         fun uu____21992  ->
                           fun uu____21993  ->
                             match (uu____21991, uu____21992, uu____21993)
                             with
                             | ((a1,uu____22029),(a2,uu____22031),(arg_sub_probs,wl2))
                                 ->
                                 let uu____22052 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____22052 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____21958 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____22081 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____22081  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____22089 = attempt sub_probs wl3  in
                       solve env uu____22089)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____22112 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22115)::[] -> wp1
              | uu____22132 ->
                  let uu____22141 =
                    let uu____22142 =
                      let uu____22143 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____22143  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____22142
                     in
                  failwith uu____22141
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____22149 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____22149]
              | x -> x  in
            let uu____22151 =
              let uu____22160 =
                let uu____22167 =
                  let uu____22168 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____22168 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____22167  in
              [uu____22160]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____22151;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____22181 = lift_c1 ()  in solve_eq uu____22181 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___336_22187  ->
                       match uu___336_22187 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____22188 -> false))
                in
             let uu____22189 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____22215)::uu____22216,(wp2,uu____22218)::uu____22219)
                   -> (wp1, wp2)
               | uu____22272 ->
                   let uu____22293 =
                     let uu____22298 =
                       let uu____22299 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____22300 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____22299 uu____22300
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____22298)
                      in
                   FStar_Errors.raise_error uu____22293
                     env.FStar_TypeChecker_Env.range
                in
             match uu____22189 with
             | (wpc1,wpc2) ->
                 let uu____22307 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____22307
                 then
                   let uu____22310 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____22310 wl
                 else
                   (let uu____22312 =
                      let uu____22319 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____22319  in
                    match uu____22312 with
                    | (c2_decl,qualifiers) ->
                        let uu____22340 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____22340
                        then
                          let c1_repr =
                            let uu____22344 =
                              let uu____22345 =
                                let uu____22346 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____22346  in
                              let uu____22347 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22345 uu____22347
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____22344
                             in
                          let c2_repr =
                            let uu____22349 =
                              let uu____22350 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____22351 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____22350 uu____22351
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____22349
                             in
                          let uu____22352 =
                            let uu____22357 =
                              let uu____22358 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____22359 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____22358 uu____22359
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____22357
                             in
                          (match uu____22352 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____22363 = attempt [prob] wl2  in
                               solve env uu____22363)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____22374 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22374
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____22377 =
                                     let uu____22384 =
                                       let uu____22385 =
                                         let uu____22400 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____22403 =
                                           let uu____22412 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____22419 =
                                             let uu____22428 =
                                               let uu____22435 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____22435
                                                in
                                             [uu____22428]  in
                                           uu____22412 :: uu____22419  in
                                         (uu____22400, uu____22403)  in
                                       FStar_Syntax_Syntax.Tm_app uu____22385
                                        in
                                     FStar_Syntax_Syntax.mk uu____22384  in
                                   uu____22377 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____22476 =
                                    let uu____22483 =
                                      let uu____22484 =
                                        let uu____22499 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____22502 =
                                          let uu____22511 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____22518 =
                                            let uu____22527 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____22534 =
                                              let uu____22543 =
                                                let uu____22550 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____22550
                                                 in
                                              [uu____22543]  in
                                            uu____22527 :: uu____22534  in
                                          uu____22511 :: uu____22518  in
                                        (uu____22499, uu____22502)  in
                                      FStar_Syntax_Syntax.Tm_app uu____22484
                                       in
                                    FStar_Syntax_Syntax.mk uu____22483  in
                                  uu____22476 FStar_Pervasives_Native.None r)
                              in
                           let uu____22594 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____22594 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____22602 =
                                   let uu____22605 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_27  ->
                                        FStar_Pervasives_Native.Some _0_27)
                                     uu____22605
                                    in
                                 solve_prob orig uu____22602 [] wl1  in
                               let uu____22608 = attempt [base_prob] wl2  in
                               solve env uu____22608)))
           in
        let uu____22609 = FStar_Util.physical_equality c1 c2  in
        if uu____22609
        then
          let uu____22610 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____22610
        else
          ((let uu____22613 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____22613
            then
              let uu____22614 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____22615 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____22614
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____22615
            else ());
           (let uu____22617 =
              let uu____22626 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____22629 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____22626, uu____22629)  in
            match uu____22617 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____22647),FStar_Syntax_Syntax.Total
                    (t2,uu____22649)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____22666 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22666 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____22667,FStar_Syntax_Syntax.Total uu____22668) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____22686),FStar_Syntax_Syntax.Total
                    (t2,uu____22688)) ->
                     let uu____22705 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22705 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____22707),FStar_Syntax_Syntax.GTotal
                    (t2,uu____22709)) ->
                     let uu____22726 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22726 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____22728),FStar_Syntax_Syntax.GTotal
                    (t2,uu____22730)) ->
                     let uu____22747 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____22747 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____22748,FStar_Syntax_Syntax.Comp uu____22749) ->
                     let uu____22758 =
                       let uu___388_22761 = problem  in
                       let uu____22764 =
                         let uu____22765 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22765
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___388_22761.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____22764;
                         FStar_TypeChecker_Common.relation =
                           (uu___388_22761.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___388_22761.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___388_22761.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___388_22761.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___388_22761.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___388_22761.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___388_22761.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___388_22761.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22758 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____22766,FStar_Syntax_Syntax.Comp uu____22767) ->
                     let uu____22776 =
                       let uu___388_22779 = problem  in
                       let uu____22782 =
                         let uu____22783 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22783
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___388_22779.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____22782;
                         FStar_TypeChecker_Common.relation =
                           (uu___388_22779.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___388_22779.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___388_22779.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___388_22779.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___388_22779.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___388_22779.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___388_22779.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___388_22779.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22776 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22784,FStar_Syntax_Syntax.GTotal uu____22785) ->
                     let uu____22794 =
                       let uu___389_22797 = problem  in
                       let uu____22800 =
                         let uu____22801 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22801
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___389_22797.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___389_22797.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___389_22797.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____22800;
                         FStar_TypeChecker_Common.element =
                           (uu___389_22797.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___389_22797.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___389_22797.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___389_22797.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___389_22797.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___389_22797.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22794 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22802,FStar_Syntax_Syntax.Total uu____22803) ->
                     let uu____22812 =
                       let uu___389_22815 = problem  in
                       let uu____22818 =
                         let uu____22819 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____22819
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___389_22815.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___389_22815.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___389_22815.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____22818;
                         FStar_TypeChecker_Common.element =
                           (uu___389_22815.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___389_22815.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___389_22815.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___389_22815.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___389_22815.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___389_22815.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____22812 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____22820,FStar_Syntax_Syntax.Comp uu____22821) ->
                     let uu____22822 =
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
                     if uu____22822
                     then
                       let uu____22823 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____22823 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____22827 =
                            let uu____22832 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____22832
                            then (c1_comp, c2_comp)
                            else
                              (let uu____22838 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____22839 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____22838, uu____22839))
                             in
                          match uu____22827 with
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
                           (let uu____22846 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____22846
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____22848 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____22848 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____22851 =
                                  let uu____22852 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____22853 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____22852 uu____22853
                                   in
                                giveup env uu____22851 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____22860 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____22888  ->
              match uu____22888 with
              | (uu____22897,tm,uu____22899,uu____22900) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____22860 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____22933 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____22933 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____22951 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____22979  ->
                match uu____22979 with
                | (u1,u2) ->
                    let uu____22986 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____22987 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____22986 uu____22987))
         in
      FStar_All.pipe_right uu____22951 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23014,[])) -> "{}"
      | uu____23039 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23062 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____23062
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____23065 =
              FStar_List.map
                (fun uu____23075  ->
                   match uu____23075 with
                   | (uu____23080,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____23065 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____23085 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23085 imps
  
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
                  let uu____23138 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____23138
                  then
                    let uu____23139 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____23140 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____23139
                      (rel_to_string rel) uu____23140
                  else "TOP"  in
                let uu____23142 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____23142 with
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
              let uu____23200 =
                let uu____23203 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____23203
                 in
              FStar_Syntax_Syntax.new_bv uu____23200 t1  in
            let uu____23206 =
              let uu____23211 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____23211
               in
            match uu____23206 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____23284 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____23284
              then
                let uu____23285 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____23285
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
          ((let uu____23307 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____23307
            then
              let uu____23308 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____23308
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____23312 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____23312
             then
               let uu____23313 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____23313
             else ());
            (let f2 =
               let uu____23316 =
                 let uu____23317 = FStar_Syntax_Util.unmeta f1  in
                 uu____23317.FStar_Syntax_Syntax.n  in
               match uu____23316 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____23321 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___390_23322 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___390_23322.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___390_23322.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___390_23322.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred,(Prims.string,FStar_Syntax_Syntax.term,
                                           FStar_Syntax_Syntax.ctx_uvar,
                                           FStar_Range.range)
                                           FStar_Pervasives_Native.tuple4
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
            let uu____23424 =
              let uu____23425 =
                let uu____23426 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____23426;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____23425  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____23424
  
let with_guard_no_simp :
  'Auu____23441 .
    'Auu____23441 ->
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
            let uu____23464 =
              let uu____23465 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____23465;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____23464
  
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
          (let uu____23503 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____23503
           then
             let uu____23504 = FStar_Syntax_Print.term_to_string t1  in
             let uu____23505 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____23504
               uu____23505
           else ());
          (let uu____23507 =
             let uu____23512 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____23512
              in
           match uu____23507 with
           | (prob,wl) ->
               let g =
                 let uu____23520 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____23538  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____23520  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23580 = try_teq true env t1 t2  in
        match uu____23580 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____23584 = FStar_TypeChecker_Env.get_range env  in
              let uu____23585 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____23584 uu____23585);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____23592 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____23592
              then
                let uu____23593 = FStar_Syntax_Print.term_to_string t1  in
                let uu____23594 = FStar_Syntax_Print.term_to_string t2  in
                let uu____23595 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____23593
                  uu____23594 uu____23595
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
          let uu____23617 = FStar_TypeChecker_Env.get_range env  in
          let uu____23618 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____23617 uu____23618
  
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
        (let uu____23643 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23643
         then
           let uu____23644 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____23645 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____23644 uu____23645
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____23648 =
           let uu____23655 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____23655 "sub_comp"
            in
         match uu____23648 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____23666 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____23684  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____23666)))
  
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
      fun uu____23737  ->
        match uu____23737 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____23780 =
                 let uu____23785 =
                   let uu____23786 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____23787 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____23786 uu____23787
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____23785)  in
               let uu____23788 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____23780 uu____23788)
               in
            let equiv1 v1 v' =
              let uu____23800 =
                let uu____23805 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____23806 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____23805, uu____23806)  in
              match uu____23800 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____23825 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____23855 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____23855 with
                      | FStar_Syntax_Syntax.U_unif uu____23862 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____23891  ->
                                    match uu____23891 with
                                    | (u,v') ->
                                        let uu____23900 = equiv1 v1 v'  in
                                        if uu____23900
                                        then
                                          let uu____23903 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____23903 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____23919 -> []))
               in
            let uu____23924 =
              let wl =
                let uu___391_23928 = empty_worklist env  in
                {
                  attempting = (uu___391_23928.attempting);
                  wl_deferred = (uu___391_23928.wl_deferred);
                  ctr = (uu___391_23928.ctr);
                  defer_ok = false;
                  smt_ok = (uu___391_23928.smt_ok);
                  tcenv = (uu___391_23928.tcenv);
                  wl_implicits = (uu___391_23928.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____23946  ->
                      match uu____23946 with
                      | (lb,v1) ->
                          let uu____23953 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____23953 with
                           | USolved wl1 -> ()
                           | uu____23955 -> fail1 lb v1)))
               in
            let rec check_ineq uu____23965 =
              match uu____23965 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____23974) -> true
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
                      uu____23997,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____23999,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24010) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24017,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24025 -> false)
               in
            let uu____24030 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24045  ->
                      match uu____24045 with
                      | (u,v1) ->
                          let uu____24052 = check_ineq (u, v1)  in
                          if uu____24052
                          then true
                          else
                            ((let uu____24055 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____24055
                              then
                                let uu____24056 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____24057 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____24056
                                  uu____24057
                              else ());
                             false)))
               in
            if uu____24030
            then ()
            else
              ((let uu____24061 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____24061
                then
                  ((let uu____24063 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____24063);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____24073 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____24073))
                else ());
               (let uu____24083 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____24083))
  
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
        let fail1 uu____24150 =
          match uu____24150 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___392_24171 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___392_24171.attempting);
            wl_deferred = (uu___392_24171.wl_deferred);
            ctr = (uu___392_24171.ctr);
            defer_ok;
            smt_ok = (uu___392_24171.smt_ok);
            tcenv = (uu___392_24171.tcenv);
            wl_implicits = (uu___392_24171.wl_implicits)
          }  in
        (let uu____24173 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____24173
         then
           let uu____24174 = FStar_Util.string_of_bool defer_ok  in
           let uu____24175 = wl_to_string wl  in
           let uu____24176 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____24174 uu____24175 uu____24176
         else ());
        (let g1 =
           let uu____24187 = solve_and_commit env wl fail1  in
           match uu____24187 with
           | FStar_Pervasives_Native.Some
               (uu____24194::uu____24195,uu____24196) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___393_24221 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___393_24221.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___393_24221.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____24230 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___394_24238 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___394_24238.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___394_24238.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___394_24238.FStar_TypeChecker_Env.implicits)
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
    let uu____24286 = FStar_ST.op_Bang last_proof_ns  in
    match uu____24286 with
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
            let uu___395_24409 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___395_24409.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___395_24409.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___395_24409.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____24410 =
            let uu____24411 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____24411  in
          if uu____24410
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____24419 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____24420 =
                       let uu____24421 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24421
                        in
                     FStar_Errors.diag uu____24419 uu____24420)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____24425 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____24426 =
                        let uu____24427 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____24427
                         in
                      FStar_Errors.diag uu____24425 uu____24426)
                   else ();
                   (let uu____24430 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____24430
                      "discharge_guard'" env vc1);
                   (let uu____24431 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____24431 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____24438 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24439 =
                                let uu____24440 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____24440
                                 in
                              FStar_Errors.diag uu____24438 uu____24439)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____24445 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____24446 =
                                let uu____24447 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____24447
                                 in
                              FStar_Errors.diag uu____24445 uu____24446)
                           else ();
                           (let vcs =
                              let uu____24458 = FStar_Options.use_tactics ()
                                 in
                              if uu____24458
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____24478  ->
                                     (let uu____24480 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____24480);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____24523  ->
                                              match uu____24523 with
                                              | (env1,goal,opts) ->
                                                  let uu____24539 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____24539, opts)))))
                              else
                                (let uu____24541 =
                                   let uu____24548 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____24548)  in
                                 [uu____24541])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____24581  ->
                                    match uu____24581 with
                                    | (env1,goal,opts) ->
                                        let uu____24591 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____24591 with
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
                                                (let uu____24599 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____24600 =
                                                   let uu____24601 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____24602 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____24601 uu____24602
                                                    in
                                                 FStar_Errors.diag
                                                   uu____24599 uu____24600)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____24605 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____24606 =
                                                   let uu____24607 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____24607
                                                    in
                                                 FStar_Errors.diag
                                                   uu____24605 uu____24606)
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
      let uu____24621 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____24621 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____24628 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____24628
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____24639 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____24639 with
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
            let uu____24672 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____24672 with
            | FStar_Pervasives_Native.Some uu____24675 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____24695 = acc  in
            match uu____24695 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____24747 = hd1  in
                     (match uu____24747 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____24761 = unresolved ctx_u  in
                             if uu____24761
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___396_24773 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___396_24773.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___396_24773.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___396_24773.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___396_24773.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___396_24773.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___396_24773.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___396_24773.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___396_24773.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___396_24773.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___396_24773.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___396_24773.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___396_24773.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___396_24773.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___396_24773.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___396_24773.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___396_24773.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___396_24773.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___396_24773.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___396_24773.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___396_24773.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___396_24773.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___396_24773.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___396_24773.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___396_24773.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___396_24773.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___396_24773.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___396_24773.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___396_24773.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___396_24773.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___396_24773.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___396_24773.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___396_24773.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___396_24773.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___396_24773.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___396_24773.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___396_24773.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___396_24773.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___396_24773.FStar_TypeChecker_Env.dep_graph);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___396_24773.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___397_24776 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___397_24776.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___397_24776.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___397_24776.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___397_24776.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___397_24776.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___397_24776.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___397_24776.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___397_24776.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___397_24776.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___397_24776.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___397_24776.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___397_24776.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___397_24776.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___397_24776.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___397_24776.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___397_24776.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___397_24776.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___397_24776.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___397_24776.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___397_24776.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___397_24776.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___397_24776.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___397_24776.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___397_24776.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___397_24776.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___397_24776.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___397_24776.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___397_24776.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___397_24776.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___397_24776.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___397_24776.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___397_24776.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___397_24776.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___397_24776.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___397_24776.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___397_24776.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___397_24776.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___397_24776.FStar_TypeChecker_Env.dep_graph);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___397_24776.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____24779 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24779
                                   then
                                     let uu____24780 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____24781 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____24782 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____24783 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____24780 uu____24781 uu____24782
                                       reason uu____24783
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____24794 =
                                             let uu____24803 =
                                               let uu____24810 =
                                                 let uu____24811 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____24812 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____24813 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____24811 uu____24812
                                                   uu____24813
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____24810, r)
                                                in
                                             [uu____24803]  in
                                           FStar_Errors.add_errors
                                             uu____24794);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___400_24827 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___400_24827.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___400_24827.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___400_24827.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____24830 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____24840  ->
                                               let uu____24841 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____24842 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____24843 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____24841 uu____24842
                                                 reason uu____24843)) env2 g2
                                         true
                                        in
                                     match uu____24830 with
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
          let uu___401_24853 = g  in
          let uu____24854 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___401_24853.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___401_24853.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___401_24853.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____24854
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
        let uu____24904 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____24904 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____24913 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____24913
      | (reason,e,ctx_u,r)::uu____24918 ->
          let uu____24937 =
            let uu____24942 =
              let uu____24943 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____24944 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____24943 uu____24944 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____24942)
             in
          FStar_Errors.raise_error uu____24937 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___402_24955 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___402_24955.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___402_24955.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___402_24955.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____24970 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____24970 with
      | FStar_Pervasives_Native.Some uu____24976 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24992 = try_teq false env t1 t2  in
        match uu____24992 with
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
        (let uu____25026 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25026
         then
           let uu____25027 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25028 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25027
             uu____25028
         else ());
        (let uu____25030 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____25030 with
         | (prob,x,wl) ->
             let g =
               let uu____25049 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____25067  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25049  in
             ((let uu____25095 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____25095
               then
                 let uu____25096 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____25097 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____25098 =
                   let uu____25099 = FStar_Util.must g  in
                   guard_to_string env uu____25099  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____25096 uu____25097 uu____25098
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
        let uu____25133 = check_subtyping env t1 t2  in
        match uu____25133 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25152 =
              let uu____25153 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____25153 g  in
            FStar_Pervasives_Native.Some uu____25152
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25171 = check_subtyping env t1 t2  in
        match uu____25171 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____25190 =
              let uu____25191 =
                let uu____25192 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____25192]  in
              FStar_TypeChecker_Env.close_guard env uu____25191 g  in
            FStar_Pervasives_Native.Some uu____25190
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____25221 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25221
         then
           let uu____25222 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____25223 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____25222
             uu____25223
         else ());
        (let uu____25225 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____25225 with
         | (prob,x,wl) ->
             let g =
               let uu____25238 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____25256  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____25238  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____25285 =
                      let uu____25286 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____25286]  in
                    FStar_TypeChecker_Env.close_guard env uu____25285 g1  in
                  discharge_guard_nosmt env g2))
  