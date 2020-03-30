open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____49 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____84 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Common.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
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
  worklist -> FStar_TypeChecker_Common.implicits) =
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
                    let uu____515 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____515;
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
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     }  in
                   (let uu____547 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____547
                    then
                      let uu____551 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____551
                    else ());
                   (ctx_uvar, t,
                     ((let uu___73_557 = wl  in
                       {
                         attempting = (uu___73_557.attempting);
                         wl_deferred = (uu___73_557.wl_deferred);
                         ctr = (uu___73_557.ctr);
                         defer_ok = (uu___73_557.defer_ok);
                         smt_ok = (uu___73_557.smt_ok);
                         umax_heuristic_ok = (uu___73_557.umax_heuristic_ok);
                         tcenv = (uu___73_557.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits))
                       }))))
  
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
            let uu___79_590 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___79_590.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___79_590.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___79_590.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___79_590.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___79_590.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___79_590.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___79_590.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___79_590.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___79_590.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___79_590.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___79_590.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___79_590.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___79_590.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___79_590.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___79_590.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___79_590.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___79_590.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___79_590.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___79_590.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___79_590.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___79_590.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___79_590.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___79_590.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___79_590.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___79_590.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___79_590.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___79_590.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___79_590.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___79_590.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___79_590.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___79_590.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___79_590.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___79_590.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___79_590.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___79_590.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___79_590.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___79_590.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___79_590.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___79_590.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___79_590.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___79_590.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___79_590.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___79_590.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___79_590.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___79_590.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___79_590.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____592 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____592 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____653 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____688 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____718 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____729 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____740 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_758  ->
    match uu___0_758 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____770 = FStar_Syntax_Util.head_and_args t  in
    match uu____770 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____833 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____835 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____850 =
                     let uu____852 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____852  in
                   FStar_Util.format1 "@<%s>" uu____850
                in
             let uu____856 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____833 uu____835 uu____856
         | uu____859 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_871  ->
      match uu___1_871 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____876 =
            let uu____880 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____882 =
              let uu____886 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____888 =
                let uu____892 =
                  let uu____896 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____896]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____892
                 in
              uu____886 :: uu____888  in
            uu____880 :: uu____882  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____876
      | FStar_TypeChecker_Common.CProb p ->
          let uu____907 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____909 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____911 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____907 uu____909
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____911
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_925  ->
      match uu___2_925 with
      | UNIV (u,t) ->
          let x =
            let uu____931 = FStar_Options.hide_uvar_nums ()  in
            if uu____931
            then "?"
            else
              (let uu____938 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____938 FStar_Util.string_of_int)
             in
          let uu____942 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____942
      | TERM (u,t) ->
          let x =
            let uu____949 = FStar_Options.hide_uvar_nums ()  in
            if uu____949
            then "?"
            else
              (let uu____956 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____956 FStar_Util.string_of_int)
             in
          let uu____960 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____960
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____979 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____979 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1000 =
      let uu____1004 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1004
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1000 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1023 .
    (FStar_Syntax_Syntax.term * 'Auu____1023) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1042 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1063  ->
              match uu____1063 with
              | (x,uu____1070) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1042 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = Prims.int_zero;
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1110 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1110
         then
           let uu____1115 = FStar_Thunk.force reason  in
           let uu____1118 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1115 uu____1118
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1141 = FStar_Thunk.mk (fun uu____1144  -> reason)  in
        giveup env uu____1141 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1150  ->
    match uu___3_1150 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1156 .
    'Auu____1156 FStar_TypeChecker_Common.problem ->
      'Auu____1156 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___143_1168 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___143_1168.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___143_1168.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___143_1168.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___143_1168.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___143_1168.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___143_1168.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___143_1168.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1176 .
    'Auu____1176 FStar_TypeChecker_Common.problem ->
      'Auu____1176 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1196  ->
    match uu___4_1196 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1202  -> FStar_TypeChecker_Common.TProb _1202)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1208  -> FStar_TypeChecker_Common.CProb _1208)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1214  ->
    match uu___5_1214 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___155_1220 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___155_1220.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___155_1220.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___155_1220.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___155_1220.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___155_1220.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___155_1220.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___155_1220.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___155_1220.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___155_1220.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___159_1228 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___159_1228.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___159_1228.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___159_1228.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___159_1228.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___159_1228.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___159_1228.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___159_1228.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___159_1228.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___159_1228.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1241  ->
      match uu___6_1241 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1248  ->
    match uu___7_1248 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1261  ->
    match uu___8_1261 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1276  ->
    match uu___9_1276 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1291  ->
    match uu___10_1291 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1305  ->
    match uu___11_1305 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1319  ->
    match uu___12_1319 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1331  ->
    match uu___13_1331 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1347 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1347) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1377 =
          let uu____1379 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1379  in
        if uu____1377
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1416)::bs ->
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
          let uu____1463 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1487 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1487]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1463
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1515 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1539 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1539]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1515
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1586 =
          let uu____1588 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1588  in
        if uu____1586
        then ()
        else
          (let uu____1593 =
             let uu____1596 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1596
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1593 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1645 =
          let uu____1647 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1647  in
        if uu____1645
        then ()
        else
          (let uu____1652 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1652)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1672 =
        let uu____1674 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1674  in
      if uu____1672
      then ()
      else
        (let msgf m =
           let uu____1688 =
             let uu____1690 =
               let uu____1692 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1692 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1690  in
           Prims.op_Hat msg uu____1688  in
         (let uu____1697 = msgf "scope"  in
          let uu____1700 = p_scope prob  in
          def_scope_wf uu____1697 (p_loc prob) uu____1700);
         (let uu____1712 = msgf "guard"  in
          def_check_scoped uu____1712 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1719 = msgf "lhs"  in
                def_check_scoped uu____1719 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1722 = msgf "rhs"  in
                def_check_scoped uu____1722 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1729 = msgf "lhs"  in
                def_check_scoped_comp uu____1729 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1732 = msgf "rhs"  in
                def_check_scoped_comp uu____1732 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___252_1753 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___252_1753.wl_deferred);
          ctr = (uu___252_1753.ctr);
          defer_ok = (uu___252_1753.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___252_1753.umax_heuristic_ok);
          tcenv = (uu___252_1753.tcenv);
          wl_implicits = (uu___252_1753.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1761 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1761 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___256_1784 = empty_worklist env  in
      let uu____1785 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1785;
        wl_deferred = (uu___256_1784.wl_deferred);
        ctr = (uu___256_1784.ctr);
        defer_ok = (uu___256_1784.defer_ok);
        smt_ok = (uu___256_1784.smt_ok);
        umax_heuristic_ok = (uu___256_1784.umax_heuristic_ok);
        tcenv = (uu___256_1784.tcenv);
        wl_implicits = (uu___256_1784.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___261_1806 = wl  in
        {
          attempting = (uu___261_1806.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___261_1806.ctr);
          defer_ok = (uu___261_1806.defer_ok);
          smt_ok = (uu___261_1806.smt_ok);
          umax_heuristic_ok = (uu___261_1806.umax_heuristic_ok);
          tcenv = (uu___261_1806.tcenv);
          wl_implicits = (uu___261_1806.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1833 = FStar_Thunk.mkv reason  in defer uu____1833 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___269_1852 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___269_1852.wl_deferred);
         ctr = (uu___269_1852.ctr);
         defer_ok = (uu___269_1852.defer_ok);
         smt_ok = (uu___269_1852.smt_ok);
         umax_heuristic_ok = (uu___269_1852.umax_heuristic_ok);
         tcenv = (uu___269_1852.tcenv);
         wl_implicits = (uu___269_1852.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1866 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1866 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1900 = FStar_Syntax_Util.type_u ()  in
            match uu____1900 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1912 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1912 with
                 | (uu____1930,tt,wl1) ->
                     let uu____1933 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1933, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1939  ->
    match uu___14_1939 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _1945  -> FStar_TypeChecker_Common.TProb _1945) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _1951  -> FStar_TypeChecker_Common.CProb _1951) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1959 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1959 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____1979  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2021 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2021 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2021 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2021 FStar_TypeChecker_Common.problem *
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
                        let uu____2108 =
                          let uu____2117 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2117]  in
                        FStar_List.append scope uu____2108
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2160 =
                      let uu____2163 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2163  in
                    FStar_List.append uu____2160
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2182 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2182 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2208 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2208;
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
                  (let uu____2282 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2282 with
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
                  (let uu____2370 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2370 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2408 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2408 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2408 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2408 FStar_TypeChecker_Common.problem *
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
                          let uu____2476 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2476]  in
                        let uu____2495 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2495
                     in
                  let uu____2498 =
                    let uu____2505 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___352_2516 = wl  in
                       {
                         attempting = (uu___352_2516.attempting);
                         wl_deferred = (uu___352_2516.wl_deferred);
                         ctr = (uu___352_2516.ctr);
                         defer_ok = (uu___352_2516.defer_ok);
                         smt_ok = (uu___352_2516.smt_ok);
                         umax_heuristic_ok =
                           (uu___352_2516.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___352_2516.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2505
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2498 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2534 =
                              let uu____2539 =
                                let uu____2540 =
                                  let uu____2549 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2549
                                   in
                                [uu____2540]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2539  in
                            uu____2534 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2577 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2577;
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
                let uu____2625 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2625;
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
  'Auu____2640 .
    worklist ->
      'Auu____2640 FStar_TypeChecker_Common.problem ->
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
              let uu____2673 =
                let uu____2676 =
                  let uu____2677 =
                    let uu____2684 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2684)  in
                  FStar_Syntax_Syntax.NT uu____2677  in
                [uu____2676]  in
              FStar_Syntax_Subst.subst uu____2673 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2706 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2706
        then
          let uu____2714 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2717 = prob_to_string env d  in
          let uu____2719 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2726 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2714 uu____2717 uu____2719 uu____2726
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2738 -> failwith "impossible"  in
           let uu____2741 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.term_to_string env)
                   tp.FStar_TypeChecker_Common.lhs
                   tp.FStar_TypeChecker_Common.rhs
             | FStar_TypeChecker_Common.CProb cp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.comp_to_string env)
                   cp.FStar_TypeChecker_Common.lhs
                   cp.FStar_TypeChecker_Common.rhs
              in
           match uu____2741 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2784  ->
            match uu___15_2784 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2796 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2800 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2800 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2831  ->
           match uu___16_2831 with
           | UNIV uu____2834 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2841 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2841
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
        (fun uu___17_2869  ->
           match uu___17_2869 with
           | UNIV (u',t) ->
               let uu____2874 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2874
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2881 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2893 =
        let uu____2894 =
          let uu____2895 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2895
           in
        FStar_Syntax_Subst.compress uu____2894  in
      FStar_All.pipe_right uu____2893 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2907 =
        let uu____2908 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2908  in
      FStar_All.pipe_right uu____2907 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2920 =
        let uu____2924 =
          let uu____2926 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2926  in
        FStar_Pervasives_Native.Some uu____2924  in
      FStar_Profiling.profile (fun uu____2929  -> sn' env t) uu____2920
        "FStar.TypeChecker.Rel.sn"
  
let (norm_with_steps :
  Prims.string ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun profiling_tag  ->
    fun steps  ->
      fun env  ->
        fun t  ->
          let uu____2954 =
            let uu____2958 =
              let uu____2960 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____2960  in
            FStar_Pervasives_Native.Some uu____2958  in
          FStar_Profiling.profile
            (fun uu____2963  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____2954
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2971 = FStar_Syntax_Util.head_and_args t  in
    match uu____2971 with
    | (h,uu____2990) ->
        let uu____3015 =
          let uu____3016 = FStar_Syntax_Subst.compress h  in
          uu____3016.FStar_Syntax_Syntax.n  in
        (match uu____3015 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3021 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3034 =
        let uu____3038 =
          let uu____3040 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3040  in
        FStar_Pervasives_Native.Some uu____3038  in
      FStar_Profiling.profile
        (fun uu____3045  ->
           let uu____3046 = should_strongly_reduce t  in
           if uu____3046
           then
             let uu____3049 =
               let uu____3050 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3050  in
             FStar_All.pipe_right uu____3049 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3034 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3061 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3061) ->
        (FStar_Syntax_Syntax.term * 'Auu____3061)
  =
  fun env  ->
    fun t  ->
      let uu____3084 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3084, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3136  ->
              match uu____3136 with
              | (x,imp) ->
                  let uu____3155 =
                    let uu___458_3156 = x  in
                    let uu____3157 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___458_3156.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___458_3156.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3157
                    }  in
                  (uu____3155, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3181 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3181
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3185 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3185
        | uu____3188 -> u2  in
      let uu____3189 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3189
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3206 =
          let uu____3210 =
            let uu____3212 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3212  in
          FStar_Pervasives_Native.Some uu____3210  in
        FStar_Profiling.profile
          (fun uu____3215  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3206 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
          normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3337 = norm_refinement env t12  in
                 match uu____3337 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3352;
                     FStar_Syntax_Syntax.vars = uu____3353;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3377 =
                       let uu____3379 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3381 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3379 uu____3381
                        in
                     failwith uu____3377)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3397 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3397
          | FStar_Syntax_Syntax.Tm_uinst uu____3398 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3435 =
                   let uu____3436 = FStar_Syntax_Subst.compress t1'  in
                   uu____3436.FStar_Syntax_Syntax.n  in
                 match uu____3435 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3451 -> aux true t1'
                 | uu____3459 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3474 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3505 =
                   let uu____3506 = FStar_Syntax_Subst.compress t1'  in
                   uu____3506.FStar_Syntax_Syntax.n  in
                 match uu____3505 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3521 -> aux true t1'
                 | uu____3529 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3544 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3591 =
                   let uu____3592 = FStar_Syntax_Subst.compress t1'  in
                   uu____3592.FStar_Syntax_Syntax.n  in
                 match uu____3591 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3607 -> aux true t1'
                 | uu____3615 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3630 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3645 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3660 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3675 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3690 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3719 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3752 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3773 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3800 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3828 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3865 ->
              let uu____3872 =
                let uu____3874 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3876 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3874 uu____3876
                 in
              failwith uu____3872
          | FStar_Syntax_Syntax.Tm_ascribed uu____3891 ->
              let uu____3918 =
                let uu____3920 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3922 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3920 uu____3922
                 in
              failwith uu____3918
          | FStar_Syntax_Syntax.Tm_delayed uu____3937 ->
              let uu____3952 =
                let uu____3954 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3956 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3954 uu____3956
                 in
              failwith uu____3952
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3971 =
                let uu____3973 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3975 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3973 uu____3975
                 in
              failwith uu____3971
           in
        let uu____3990 = whnf env t1  in aux false uu____3990
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____4035 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4035 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4076 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4076, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4103 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4103 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4163  ->
    match uu____4163 with
    | (t_base,refopt) ->
        let uu____4194 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4194 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4236 =
      let uu____4240 =
        let uu____4243 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4268  ->
                  match uu____4268 with | (uu____4276,uu____4277,x) -> x))
           in
        FStar_List.append wl.attempting uu____4243  in
      FStar_List.map (wl_prob_to_string wl) uu____4240  in
    FStar_All.pipe_right uu____4236 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4298 .
    ('Auu____4298 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4310  ->
    match uu____4310 with
    | (uu____4317,c,args) ->
        let uu____4320 = print_ctx_uvar c  in
        let uu____4322 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4320 uu____4322
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4332 = FStar_Syntax_Util.head_and_args t  in
    match uu____4332 with
    | (head1,_args) ->
        let uu____4376 =
          let uu____4377 = FStar_Syntax_Subst.compress head1  in
          uu____4377.FStar_Syntax_Syntax.n  in
        (match uu____4376 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4381 -> true
         | uu____4395 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4403 = FStar_Syntax_Util.head_and_args t  in
    match uu____4403 with
    | (head1,_args) ->
        let uu____4446 =
          let uu____4447 = FStar_Syntax_Subst.compress head1  in
          uu____4447.FStar_Syntax_Syntax.n  in
        (match uu____4446 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4451) -> u
         | uu____4468 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4493 = FStar_Syntax_Util.head_and_args t  in
      match uu____4493 with
      | (head1,args) ->
          let uu____4540 =
            let uu____4541 = FStar_Syntax_Subst.compress head1  in
            uu____4541.FStar_Syntax_Syntax.n  in
          (match uu____4540 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4549)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4582 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4607  ->
                         match uu___18_4607 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4612 =
                               let uu____4613 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4613.FStar_Syntax_Syntax.n  in
                             (match uu____4612 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4618 -> false)
                         | uu____4620 -> true))
                  in
               (match uu____4582 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4645 =
                        FStar_List.collect
                          (fun uu___19_4657  ->
                             match uu___19_4657 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4661 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4661]
                             | uu____4662 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4645 FStar_List.rev  in
                    let uu____4685 =
                      let uu____4692 =
                        let uu____4701 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4723  ->
                                  match uu___20_4723 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4727 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4727]
                                  | uu____4728 -> []))
                           in
                        FStar_All.pipe_right uu____4701 FStar_List.rev  in
                      let uu____4751 =
                        let uu____4754 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4754  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4692 uu____4751
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4685 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4790  ->
                                match uu____4790 with
                                | (x,i) ->
                                    let uu____4809 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4809, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4840  ->
                                match uu____4840 with
                                | (a,i) ->
                                    let uu____4859 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4859, i)) args_sol
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
           | uu____4881 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4903 =
          let uu____4926 =
            let uu____4927 = FStar_Syntax_Subst.compress k  in
            uu____4927.FStar_Syntax_Syntax.n  in
          match uu____4926 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5009 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5009)
              else
                (let uu____5044 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5044 with
                 | (ys',t1,uu____5077) ->
                     let uu____5082 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5082))
          | uu____5121 ->
              let uu____5122 =
                let uu____5127 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5127)  in
              ((ys, t), uu____5122)
           in
        match uu____4903 with
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
                 let uu____5222 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5222 c  in
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
               (let uu____5300 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5300
                then
                  let uu____5305 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5307 = print_ctx_uvar uv  in
                  let uu____5309 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5305 uu____5307 uu____5309
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5318 =
                   let uu____5320 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5320  in
                 let uu____5323 =
                   let uu____5326 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5326
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5318 uu____5323 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5359 =
               let uu____5360 =
                 let uu____5362 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5364 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5362 uu____5364
                  in
               failwith uu____5360  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5430  ->
                       match uu____5430 with
                       | (a,i) ->
                           let uu____5451 =
                             let uu____5452 = FStar_Syntax_Subst.compress a
                                in
                             uu____5452.FStar_Syntax_Syntax.n  in
                           (match uu____5451 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5478 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5488 =
                 let uu____5490 = is_flex g  in Prims.op_Negation uu____5490
                  in
               if uu____5488
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5499 = destruct_flex_t g wl  in
                  match uu____5499 with
                  | ((uu____5504,uv1,args),wl1) ->
                      ((let uu____5509 = args_as_binders args  in
                        assign_solution uu____5509 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___711_5511 = wl1  in
              {
                attempting = (uu___711_5511.attempting);
                wl_deferred = (uu___711_5511.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___711_5511.defer_ok);
                smt_ok = (uu___711_5511.smt_ok);
                umax_heuristic_ok = (uu___711_5511.umax_heuristic_ok);
                tcenv = (uu___711_5511.tcenv);
                wl_implicits = (uu___711_5511.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5536 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5536
         then
           let uu____5541 = FStar_Util.string_of_int pid  in
           let uu____5543 =
             let uu____5545 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5545 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5541 uu____5543
         else ());
        commit sol;
        (let uu___719_5559 = wl  in
         {
           attempting = (uu___719_5559.attempting);
           wl_deferred = (uu___719_5559.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___719_5559.defer_ok);
           smt_ok = (uu___719_5559.smt_ok);
           umax_heuristic_ok = (uu___719_5559.umax_heuristic_ok);
           tcenv = (uu___719_5559.tcenv);
           wl_implicits = (uu___719_5559.wl_implicits)
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
          (let uu____5595 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5595
           then
             let uu____5600 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5604 =
               let uu____5606 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5606 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5600 uu____5604
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____5641 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5641 FStar_Util.set_elements  in
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
      let uu____5681 = occurs uk t  in
      match uu____5681 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5720 =
                 let uu____5722 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5724 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5722 uu____5724
                  in
               FStar_Pervasives_Native.Some uu____5720)
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
            let uu____5844 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5844 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5895 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5952  ->
             match uu____5952 with
             | (x,uu____5964) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5982 = FStar_List.last bs  in
      match uu____5982 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6006) ->
          let uu____6017 =
            FStar_Util.prefix_until
              (fun uu___21_6032  ->
                 match uu___21_6032 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6035 -> false) g
             in
          (match uu____6017 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6049,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6086 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6086 with
        | (pfx,uu____6096) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6108 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6108 with
             | (uu____6116,src',wl1) ->
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
                 | uu____6230 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6231 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6295  ->
                  fun uu____6296  ->
                    match (uu____6295, uu____6296) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6399 =
                          let uu____6401 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6401
                           in
                        if uu____6399
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6435 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6435
                           then
                             let uu____6452 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6452)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6231 with | (isect,uu____6502) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6538 'Auu____6539 .
    (FStar_Syntax_Syntax.bv * 'Auu____6538) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6539) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6597  ->
              fun uu____6598  ->
                match (uu____6597, uu____6598) with
                | ((a,uu____6617),(b,uu____6619)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6635 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6635) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6666  ->
           match uu____6666 with
           | (y,uu____6673) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6683 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6683) Prims.list ->
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
                   let uu____6845 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6845
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6878 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6930 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6974 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6995 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7003  ->
    match uu___22_7003 with
    | MisMatch (d1,d2) ->
        let uu____7015 =
          let uu____7017 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7019 =
            let uu____7021 =
              let uu____7023 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7023 ")"  in
            Prims.op_Hat ") (" uu____7021  in
          Prims.op_Hat uu____7017 uu____7019  in
        Prims.op_Hat "MisMatch (" uu____7015
    | HeadMatch u ->
        let uu____7030 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7030
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7039  ->
    match uu___23_7039 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7056 -> HeadMatch false
  
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
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7078 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7078 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7089 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7113 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7123 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7142 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7142
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7143 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7144 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7145 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7158 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7172 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7196) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7202,uu____7203) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7245) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7270;
             FStar_Syntax_Syntax.index = uu____7271;
             FStar_Syntax_Syntax.sort = t2;_},uu____7273)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7281 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7282 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7283 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7298 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7305 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7325 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7325
  
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
           { FStar_Syntax_Syntax.blob = uu____7344;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7345;
             FStar_Syntax_Syntax.ltyp = uu____7346;
             FStar_Syntax_Syntax.rng = uu____7347;_},uu____7348)
            ->
            let uu____7359 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7359 t21
        | (uu____7360,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7361;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7362;
             FStar_Syntax_Syntax.ltyp = uu____7363;
             FStar_Syntax_Syntax.rng = uu____7364;_})
            ->
            let uu____7375 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7375
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7387 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7387
            then FullMatch
            else
              (let uu____7392 =
                 let uu____7401 =
                   let uu____7404 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7404  in
                 let uu____7405 =
                   let uu____7408 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7408  in
                 (uu____7401, uu____7405)  in
               MisMatch uu____7392)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7414),FStar_Syntax_Syntax.Tm_uinst (g,uu____7416)) ->
            let uu____7425 = head_matches env f g  in
            FStar_All.pipe_right uu____7425 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7426) -> HeadMatch true
        | (uu____7428,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7432 = FStar_Const.eq_const c d  in
            if uu____7432
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7442),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7444)) ->
            let uu____7477 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7477
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7487),FStar_Syntax_Syntax.Tm_refine (y,uu____7489)) ->
            let uu____7498 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7498 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7500),uu____7501) ->
            let uu____7506 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7506 head_match
        | (uu____7507,FStar_Syntax_Syntax.Tm_refine (x,uu____7509)) ->
            let uu____7514 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7514 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7515,FStar_Syntax_Syntax.Tm_type
           uu____7516) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7518,FStar_Syntax_Syntax.Tm_arrow uu____7519) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7550),FStar_Syntax_Syntax.Tm_app (head',uu____7552))
            ->
            let uu____7601 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7601 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7603),uu____7604) ->
            let uu____7629 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7629 head_match
        | (uu____7630,FStar_Syntax_Syntax.Tm_app (head1,uu____7632)) ->
            let uu____7657 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7657 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7658,FStar_Syntax_Syntax.Tm_let
           uu____7659) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7687,FStar_Syntax_Syntax.Tm_match uu____7688) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7734,FStar_Syntax_Syntax.Tm_abs
           uu____7735) -> HeadMatch true
        | uu____7773 ->
            let uu____7778 =
              let uu____7787 = delta_depth_of_term env t11  in
              let uu____7790 = delta_depth_of_term env t21  in
              (uu____7787, uu____7790)  in
            MisMatch uu____7778
  
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
              let uu____7859 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7859  in
            (let uu____7861 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7861
             then
               let uu____7866 = FStar_Syntax_Print.term_to_string t  in
               let uu____7868 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7866 uu____7868
             else ());
            (let uu____7873 =
               let uu____7874 = FStar_Syntax_Util.un_uinst head1  in
               uu____7874.FStar_Syntax_Syntax.n  in
             match uu____7873 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7880 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7880 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7894 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7894
                        then
                          let uu____7899 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7899
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7904 ->
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
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.1" steps env
                          t
                         in
                      let uu____7922 =
                        let uu____7924 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7924 = FStar_Syntax_Util.Equal  in
                      if uu____7922
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7931 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7931
                          then
                            let uu____7936 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7938 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7936
                              uu____7938
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7943 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry1 n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8095 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8095
             then
               let uu____8100 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8102 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8104 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8100
                 uu____8102 uu____8104
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8132 =
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
               match uu____8132 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8180 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8180 with
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
                   aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____8218),uu____8219)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8240 =
                      let uu____8249 = maybe_inline t11  in
                      let uu____8252 = maybe_inline t21  in
                      (uu____8249, uu____8252)  in
                    match uu____8240 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu____8295,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8296))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8317 =
                      let uu____8326 = maybe_inline t11  in
                      let uu____8329 = maybe_inline t21  in
                      (uu____8326, uu____8329)  in
                    match uu____8317 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____8384 -> fail1 n_delta r t11 t21
             | uu____8393 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8408 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8408
           then
             let uu____8413 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8415 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8417 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8425 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8442 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8442
                    (fun uu____8477  ->
                       match uu____8477 with
                       | (t11,t21) ->
                           let uu____8485 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8487 =
                             let uu____8489 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8489  in
                           Prims.op_Hat uu____8485 uu____8487))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8413 uu____8415 uu____8417 uu____8425
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8506 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8506 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8521  ->
    match uu___24_8521 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.of_int (5))
  
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
      let uu___1208_8570 = p  in
      let uu____8573 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8574 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1208_8570.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8573;
        FStar_TypeChecker_Common.relation =
          (uu___1208_8570.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8574;
        FStar_TypeChecker_Common.element =
          (uu___1208_8570.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1208_8570.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1208_8570.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1208_8570.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1208_8570.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1208_8570.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8589 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8589
            (fun _8594  -> FStar_TypeChecker_Common.TProb _8594)
      | FStar_TypeChecker_Common.CProb uu____8595 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8618 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8618 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8626 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8626 with
           | (lh,lhs_args) ->
               let uu____8673 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8673 with
                | (rh,rhs_args) ->
                    let uu____8720 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8733,FStar_Syntax_Syntax.Tm_uvar uu____8734)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8823 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8850,uu____8851)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8866,FStar_Syntax_Syntax.Tm_uvar uu____8867)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8882,FStar_Syntax_Syntax.Tm_arrow uu____8883)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8913 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8913.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8913.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8913.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8913.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8913.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8913.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8913.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8913.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8913.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8916,FStar_Syntax_Syntax.Tm_type uu____8917)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8933 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8933.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8933.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8933.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8933.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8933.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8933.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8933.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8933.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8933.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8936,FStar_Syntax_Syntax.Tm_uvar uu____8937)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1259_8953 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1259_8953.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1259_8953.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1259_8953.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1259_8953.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1259_8953.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1259_8953.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1259_8953.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1259_8953.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1259_8953.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8956,FStar_Syntax_Syntax.Tm_uvar uu____8957)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8972,uu____8973)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8988,FStar_Syntax_Syntax.Tm_uvar uu____8989)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9004,uu____9005) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8720 with
                     | (rank,tp1) ->
                         let uu____9018 =
                           FStar_All.pipe_right
                             (let uu___1279_9022 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1279_9022.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1279_9022.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1279_9022.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1279_9022.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1279_9022.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1279_9022.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1279_9022.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1279_9022.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1279_9022.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9025  ->
                                FStar_TypeChecker_Common.TProb _9025)
                            in
                         (rank, uu____9018))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9029 =
            FStar_All.pipe_right
              (let uu___1283_9033 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1283_9033.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1283_9033.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1283_9033.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1283_9033.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1283_9033.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1283_9033.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1283_9033.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1283_9033.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1283_9033.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9036  -> FStar_TypeChecker_Common.CProb _9036)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9029)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9096 probs =
      match uu____9096 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9177 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9198 = rank wl.tcenv hd1  in
               (match uu____9198 with
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
                      (let uu____9259 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9264 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9264)
                          in
                       if uu____9259
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
          let uu____9337 = FStar_Syntax_Util.head_and_args t  in
          match uu____9337 with
          | (hd1,uu____9356) ->
              let uu____9381 =
                let uu____9382 = FStar_Syntax_Subst.compress hd1  in
                uu____9382.FStar_Syntax_Syntax.n  in
              (match uu____9381 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9387) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9422  ->
                           match uu____9422 with
                           | (y,uu____9431) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9454  ->
                                       match uu____9454 with
                                       | (x,uu____9463) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9468 -> false)
           in
        let uu____9470 = rank tcenv p  in
        match uu____9470 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9479 -> true
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
  | UFailed of lstring 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9534 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9553 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9572 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9589 = FStar_Thunk.mkv s  in UFailed uu____9589 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9604 = FStar_Thunk.mk s  in UFailed uu____9604 
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
                        let uu____9656 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9656 with
                        | (k,uu____9664) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9677 -> false)))
            | uu____9679 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9731 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9739 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9739 = Prims.int_zero))
                           in
                        if uu____9731 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9760 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9768 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9768 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9760)
               in
            let uu____9772 = filter1 u12  in
            let uu____9775 = filter1 u22  in (uu____9772, uu____9775)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9810 = filter_out_common_univs us1 us2  in
                   (match uu____9810 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9870 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9870 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9873 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9890  ->
                               let uu____9891 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9893 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9891 uu____9893))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9919 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9919 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9945 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9945 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9948 ->
                   ufailed_thunk
                     (fun uu____9959  ->
                        let uu____9960 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____9962 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9960 uu____9962 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9965,uu____9966) ->
              let uu____9968 =
                let uu____9970 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9972 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9970 uu____9972
                 in
              failwith uu____9968
          | (FStar_Syntax_Syntax.U_unknown ,uu____9975) ->
              let uu____9976 =
                let uu____9978 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9980 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9978 uu____9980
                 in
              failwith uu____9976
          | (uu____9983,FStar_Syntax_Syntax.U_bvar uu____9984) ->
              let uu____9986 =
                let uu____9988 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9990 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9988 uu____9990
                 in
              failwith uu____9986
          | (uu____9993,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9994 =
                let uu____9996 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9998 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9996 uu____9998
                 in
              failwith uu____9994
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10028 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10028
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10045 = occurs_univ v1 u3  in
              if uu____10045
              then
                let uu____10048 =
                  let uu____10050 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10052 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10050 uu____10052
                   in
                try_umax_components u11 u21 uu____10048
              else
                (let uu____10057 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10057)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10069 = occurs_univ v1 u3  in
              if uu____10069
              then
                let uu____10072 =
                  let uu____10074 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10076 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10074 uu____10076
                   in
                try_umax_components u11 u21 uu____10072
              else
                (let uu____10081 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10081)
          | (FStar_Syntax_Syntax.U_max uu____10082,uu____10083) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10091 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10091
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10097,FStar_Syntax_Syntax.U_max uu____10098) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10106 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10106
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10112,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10114,FStar_Syntax_Syntax.U_name uu____10115) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10117) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10119) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10121,FStar_Syntax_Syntax.U_succ uu____10122) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10124,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
  
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
      let uu____10231 = bc1  in
      match uu____10231 with
      | (bs1,mk_cod1) ->
          let uu____10275 = bc2  in
          (match uu____10275 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10386 = aux xs ys  in
                     (match uu____10386 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10469 =
                       let uu____10476 = mk_cod1 xs  in ([], uu____10476)  in
                     let uu____10479 =
                       let uu____10486 = mk_cod2 ys  in ([], uu____10486)  in
                     (uu____10469, uu____10479)
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
                  let uu____10555 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10555 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10558 =
                    let uu____10559 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10559 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10558
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10564 = has_type_guard t1 t2  in (uu____10564, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10565 = has_type_guard t2 t1  in (uu____10565, wl)
  
let is_flex_pat :
  'Auu____10575 'Auu____10576 'Auu____10577 .
    ('Auu____10575 * 'Auu____10576 * 'Auu____10577 Prims.list) -> Prims.bool
  =
  fun uu___25_10591  ->
    match uu___25_10591 with
    | (uu____10600,uu____10601,[]) -> true
    | uu____10605 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10638 = f  in
      match uu____10638 with
      | (uu____10645,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10646;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10647;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10650;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10651;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10652;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10653;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10723  ->
                 match uu____10723 with
                 | (y,uu____10732) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10886 =
                  let uu____10901 =
                    let uu____10904 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10904  in
                  ((FStar_List.rev pat_binders), uu____10901)  in
                FStar_Pervasives_Native.Some uu____10886
            | (uu____10937,[]) ->
                let uu____10968 =
                  let uu____10983 =
                    let uu____10986 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10986  in
                  ((FStar_List.rev pat_binders), uu____10983)  in
                FStar_Pervasives_Native.Some uu____10968
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11077 =
                  let uu____11078 = FStar_Syntax_Subst.compress a  in
                  uu____11078.FStar_Syntax_Syntax.n  in
                (match uu____11077 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11098 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11098
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1611_11128 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1611_11128.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1611_11128.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11132 =
                            let uu____11133 =
                              let uu____11140 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11140)  in
                            FStar_Syntax_Syntax.NT uu____11133  in
                          [uu____11132]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1617_11156 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1617_11156.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1617_11156.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11157 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11197 =
                  let uu____11204 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11204  in
                (match uu____11197 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11263 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11288 ->
               let uu____11289 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11289 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11585 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11585
       then
         let uu____11590 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11590
       else ());
      (let uu____11596 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11596
       then
         let uu____11601 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11601
       else ());
      (let uu____11606 = next_prob probs  in
       match uu____11606 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1644_11633 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1644_11633.wl_deferred);
               ctr = (uu___1644_11633.ctr);
               defer_ok = (uu___1644_11633.defer_ok);
               smt_ok = (uu___1644_11633.smt_ok);
               umax_heuristic_ok = (uu___1644_11633.umax_heuristic_ok);
               tcenv = (uu___1644_11633.tcenv);
               wl_implicits = (uu___1644_11633.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11642 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11642
                 then
                   let uu____11645 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11645
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
                       (let uu____11652 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11652)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1656_11658 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1656_11658.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1656_11658.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1656_11658.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1656_11658.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1656_11658.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1656_11658.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1656_11658.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1656_11658.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1656_11658.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11683 ->
                let uu____11693 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11758  ->
                          match uu____11758 with
                          | (c,uu____11768,uu____11769) -> c < probs.ctr))
                   in
                (match uu____11693 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11817 =
                            let uu____11822 =
                              FStar_List.map
                                (fun uu____11843  ->
                                   match uu____11843 with
                                   | (uu____11859,x,y) ->
                                       let uu____11870 = FStar_Thunk.force x
                                          in
                                       (uu____11870, y)) probs.wl_deferred
                               in
                            (uu____11822, (probs.wl_implicits))  in
                          Success uu____11817
                      | uu____11874 ->
                          let uu____11884 =
                            let uu___1674_11885 = probs  in
                            let uu____11886 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11907  ->
                                      match uu____11907 with
                                      | (uu____11915,uu____11916,y) -> y))
                               in
                            {
                              attempting = uu____11886;
                              wl_deferred = rest;
                              ctr = (uu___1674_11885.ctr);
                              defer_ok = (uu___1674_11885.defer_ok);
                              smt_ok = (uu___1674_11885.smt_ok);
                              umax_heuristic_ok =
                                (uu___1674_11885.umax_heuristic_ok);
                              tcenv = (uu___1674_11885.tcenv);
                              wl_implicits = (uu___1674_11885.wl_implicits)
                            }  in
                          solve env uu____11884))))

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
            let uu____11925 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11925 with
            | USolved wl1 ->
                let uu____11927 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11927
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11930 = defer_lit "" orig wl1  in
                solve env uu____11930

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
                  let uu____11981 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____11981 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11984 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11997;
                  FStar_Syntax_Syntax.vars = uu____11998;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12001;
                  FStar_Syntax_Syntax.vars = uu____12002;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12015,uu____12016) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12024,FStar_Syntax_Syntax.Tm_uinst uu____12025) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12033 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> lstring -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____12044 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12044
              then
                let uu____12049 = prob_to_string env orig  in
                let uu____12051 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12049 uu____12051
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
               let uu____12144 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12144 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12199 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12199
                then
                  let uu____12204 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12206 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12204 uu____12206
                else ());
               (let uu____12211 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12211 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12257 = eq_prob t1 t2 wl2  in
                         (match uu____12257 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12278 ->
                         let uu____12287 = eq_prob t1 t2 wl2  in
                         (match uu____12287 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12337 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12352 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12353 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12352, uu____12353)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12358 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12359 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12358, uu____12359)
                            in
                         (match uu____12337 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12390 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12390 with
                                | (t1_hd,t1_args) ->
                                    let uu____12435 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12435 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12501 =
                                              let uu____12508 =
                                                let uu____12519 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12519 :: t1_args  in
                                              let uu____12536 =
                                                let uu____12545 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12545 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12594  ->
                                                   fun uu____12595  ->
                                                     fun uu____12596  ->
                                                       match (uu____12594,
                                                               uu____12595,
                                                               uu____12596)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12646),
                                                          (a2,uu____12648))
                                                           ->
                                                           let uu____12685 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12685
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12508
                                                uu____12536
                                               in
                                            match uu____12501 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1828_12711 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1828_12711.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1828_12711.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1828_12711.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12722 =
                                                  solve env1 wl'  in
                                                (match uu____12722 with
                                                 | Success (uu____12725,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1837_12729
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1837_12729.attempting);
                                                            wl_deferred =
                                                              (uu___1837_12729.wl_deferred);
                                                            ctr =
                                                              (uu___1837_12729.ctr);
                                                            defer_ok =
                                                              (uu___1837_12729.defer_ok);
                                                            smt_ok =
                                                              (uu___1837_12729.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1837_12729.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1837_12729.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12730 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12762 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12762 with
                                | (t1_base,p1_opt) ->
                                    let uu____12798 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12798 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12897 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12897
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
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____12950 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12950
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____12982 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____12982
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13014 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13014
                                           | uu____13017 -> t_base  in
                                         let uu____13034 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13034 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13048 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13048, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13055 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13055 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13091 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13091 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13127 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13127
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
                              let uu____13151 = combine t11 t21 wl2  in
                              (match uu____13151 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13184 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13184
                                     then
                                       let uu____13189 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13189
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13231 ts1 =
               match uu____13231 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13294 = pairwise out t wl2  in
                        (match uu____13294 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13330 =
               let uu____13341 = FStar_List.hd ts  in (uu____13341, [], wl1)
                in
             let uu____13350 = FStar_List.tl ts  in
             aux uu____13330 uu____13350  in
           let uu____13357 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13357 with
           | (this_flex,this_rigid) ->
               let uu____13383 =
                 let uu____13384 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13384.FStar_Syntax_Syntax.n  in
               (match uu____13383 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13409 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13409
                    then
                      let uu____13412 = destruct_flex_t this_flex wl  in
                      (match uu____13412 with
                       | (flex,wl1) ->
                           let uu____13419 = quasi_pattern env flex  in
                           (match uu____13419 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13438 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13438
                                  then
                                    let uu____13443 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13443
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13450 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1939_13453 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1939_13453.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1939_13453.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1939_13453.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1939_13453.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1939_13453.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1939_13453.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1939_13453.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1939_13453.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1939_13453.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13450)
                | uu____13454 ->
                    ((let uu____13456 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13456
                      then
                        let uu____13461 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13461
                      else ());
                     (let uu____13466 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13466 with
                      | (u,_args) ->
                          let uu____13509 =
                            let uu____13510 = FStar_Syntax_Subst.compress u
                               in
                            uu____13510.FStar_Syntax_Syntax.n  in
                          (match uu____13509 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13538 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13538 with
                                 | (u',uu____13557) ->
                                     let uu____13582 =
                                       let uu____13583 = whnf env u'  in
                                       uu____13583.FStar_Syntax_Syntax.n  in
                                     (match uu____13582 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13605 -> false)
                                  in
                               let uu____13607 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13630  ->
                                         match uu___26_13630 with
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
                                              | uu____13644 -> false)
                                         | uu____13648 -> false))
                                  in
                               (match uu____13607 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13663 = whnf env this_rigid
                                         in
                                      let uu____13664 =
                                        FStar_List.collect
                                          (fun uu___27_13670  ->
                                             match uu___27_13670 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13676 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13676]
                                             | uu____13680 -> [])
                                          bounds_probs
                                         in
                                      uu____13663 :: uu____13664  in
                                    let uu____13681 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13681 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13714 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13729 =
                                               let uu____13730 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13730.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13729 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13742 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13742)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13753 -> bound  in
                                           let uu____13754 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13754)  in
                                         (match uu____13714 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13789 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13789
                                                then
                                                  let wl'1 =
                                                    let uu___1999_13795 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1999_13795.wl_deferred);
                                                      ctr =
                                                        (uu___1999_13795.ctr);
                                                      defer_ok =
                                                        (uu___1999_13795.defer_ok);
                                                      smt_ok =
                                                        (uu___1999_13795.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1999_13795.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1999_13795.tcenv);
                                                      wl_implicits =
                                                        (uu___1999_13795.wl_implicits)
                                                    }  in
                                                  let uu____13796 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13796
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13802 =
                                                  solve_t env eq_prob
                                                    (let uu___2004_13804 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2004_13804.wl_deferred);
                                                       ctr =
                                                         (uu___2004_13804.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2004_13804.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2004_13804.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2004_13804.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13802 with
                                                | Success (uu____13806,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2010_13809 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2010_13809.wl_deferred);
                                                        ctr =
                                                          (uu___2010_13809.ctr);
                                                        defer_ok =
                                                          (uu___2010_13809.defer_ok);
                                                        smt_ok =
                                                          (uu___2010_13809.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2010_13809.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2010_13809.tcenv);
                                                        wl_implicits =
                                                          (uu___2010_13809.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2013_13811 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2013_13811.attempting);
                                                        wl_deferred =
                                                          (uu___2013_13811.wl_deferred);
                                                        ctr =
                                                          (uu___2013_13811.ctr);
                                                        defer_ok =
                                                          (uu___2013_13811.defer_ok);
                                                        smt_ok =
                                                          (uu___2013_13811.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2013_13811.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2013_13811.tcenv);
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
                                                    let uu____13827 =
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
                                                    ((let uu____13839 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13839
                                                      then
                                                        let uu____13844 =
                                                          let uu____13846 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13846
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13844
                                                      else ());
                                                     (let uu____13859 =
                                                        let uu____13874 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13874)
                                                         in
                                                      match uu____13859 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13896))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13922 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13922
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
                                                                  let uu____13942
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13942))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13967 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13967
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
                                                                    let uu____13987
                                                                    =
                                                                    let uu____13992
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13992
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13987
                                                                    [] wl2
                                                                     in
                                                                  let uu____13998
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13998))))
                                                      | uu____13999 ->
                                                          let uu____14014 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14014 p)))))))
                           | uu____14021 when flip ->
                               let uu____14022 =
                                 let uu____14024 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14026 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14024 uu____14026
                                  in
                               failwith uu____14022
                           | uu____14029 ->
                               let uu____14030 =
                                 let uu____14032 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14034 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14032 uu____14034
                                  in
                               failwith uu____14030)))))

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
                      (fun uu____14070  ->
                         match uu____14070 with
                         | (x,i) ->
                             let uu____14089 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14089, i)) bs_lhs
                     in
                  let uu____14092 = lhs  in
                  match uu____14092 with
                  | (uu____14093,u_lhs,uu____14095) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14192 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14202 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14202, univ)
                             in
                          match uu____14192 with
                          | (k,univ) ->
                              let uu____14209 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14209 with
                               | (uu____14226,u,wl3) ->
                                   let uu____14229 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14229, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14255 =
                              let uu____14268 =
                                let uu____14279 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14279 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14330  ->
                                   fun uu____14331  ->
                                     match (uu____14330, uu____14331) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14432 =
                                           let uu____14439 =
                                             let uu____14442 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14442
                                              in
                                           copy_uvar u_lhs [] uu____14439 wl2
                                            in
                                         (match uu____14432 with
                                          | (uu____14471,t_a,wl3) ->
                                              let uu____14474 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14474 with
                                               | (uu____14493,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14268
                                ([], wl1)
                               in
                            (match uu____14255 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2124_14549 = ct  in
                                   let uu____14550 =
                                     let uu____14553 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14553
                                      in
                                   let uu____14568 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2124_14549.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2124_14549.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14550;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14568;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2124_14549.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2127_14586 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2127_14586.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2127_14586.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14589 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14589 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14627 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14627 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14638 =
                                          let uu____14643 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14643)  in
                                        TERM uu____14638  in
                                      let uu____14644 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14644 with
                                       | (sub_prob,wl3) ->
                                           let uu____14658 =
                                             let uu____14659 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14659
                                              in
                                           solve env uu____14658))
                             | (x,imp)::formals2 ->
                                 let uu____14681 =
                                   let uu____14688 =
                                     let uu____14691 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14691
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14688 wl1
                                    in
                                 (match uu____14681 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14712 =
                                          let uu____14715 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14715
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14712 u_x
                                         in
                                      let uu____14716 =
                                        let uu____14719 =
                                          let uu____14722 =
                                            let uu____14723 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14723, imp)  in
                                          [uu____14722]  in
                                        FStar_List.append bs_terms
                                          uu____14719
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14716 formals2 wl2)
                              in
                           let uu____14750 = occurs_check u_lhs arrow1  in
                           (match uu____14750 with
                            | (uu____14763,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14779 =
                                    FStar_Thunk.mk
                                      (fun uu____14783  ->
                                         let uu____14784 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14784)
                                     in
                                  giveup_or_defer env orig wl uu____14779
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
              (let uu____14817 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14817
               then
                 let uu____14822 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14825 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14822 (rel_to_string (p_rel orig)) uu____14825
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____14956 = rhs wl1 scope env1 subst1  in
                     (match uu____14956 with
                      | (rhs_prob,wl2) ->
                          ((let uu____14979 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14979
                            then
                              let uu____14984 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14984
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15062 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15062 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2197_15064 = hd1  in
                       let uu____15065 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2197_15064.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2197_15064.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15065
                       }  in
                     let hd21 =
                       let uu___2200_15069 = hd2  in
                       let uu____15070 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2200_15069.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2200_15069.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15070
                       }  in
                     let uu____15073 =
                       let uu____15078 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15078
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15073 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15101 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15101
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15108 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15108 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15180 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15180
                                  in
                               ((let uu____15198 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15198
                                 then
                                   let uu____15203 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15205 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15203
                                     uu____15205
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15240 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15276 = aux wl [] env [] bs1 bs2  in
               match uu____15276 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15335 = attempt sub_probs wl2  in
                   solve env1 uu____15335)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist -> (FStar_TypeChecker_Common.prob * lstring) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2238_15355 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2238_15355.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2238_15355.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15367 = try_solve env wl'  in
          match uu____15367 with
          | Success (uu____15368,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2247_15372 = wl  in
                  {
                    attempting = (uu___2247_15372.attempting);
                    wl_deferred = (uu___2247_15372.wl_deferred);
                    ctr = (uu___2247_15372.ctr);
                    defer_ok = (uu___2247_15372.defer_ok);
                    smt_ok = (uu___2247_15372.smt_ok);
                    umax_heuristic_ok = (uu___2247_15372.umax_heuristic_ok);
                    tcenv = (uu___2247_15372.tcenv);
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
        (let uu____15381 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15381 wl)

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
              let uu____15395 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15395 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15429 = lhs1  in
              match uu____15429 with
              | (uu____15432,ctx_u,uu____15434) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15442 ->
                        let uu____15443 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15443 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15492 = quasi_pattern env1 lhs1  in
              match uu____15492 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15526) ->
                  let uu____15531 = lhs1  in
                  (match uu____15531 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15546 = occurs_check ctx_u rhs1  in
                       (match uu____15546 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15597 =
                                let uu____15605 =
                                  let uu____15607 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15607
                                   in
                                FStar_Util.Inl uu____15605  in
                              (uu____15597, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15635 =
                                 let uu____15637 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15637  in
                               if uu____15635
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15664 =
                                    let uu____15672 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15672  in
                                  let uu____15678 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15664, uu____15678)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15722 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15722 with
              | (rhs_hd,args) ->
                  let uu____15765 = FStar_Util.prefix args  in
                  (match uu____15765 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15837 = lhs1  in
                       (match uu____15837 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15841 =
                              let uu____15852 =
                                let uu____15859 =
                                  let uu____15862 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15862
                                   in
                                copy_uvar u_lhs [] uu____15859 wl1  in
                              match uu____15852 with
                              | (uu____15889,t_last_arg,wl2) ->
                                  let uu____15892 =
                                    let uu____15899 =
                                      let uu____15900 =
                                        let uu____15909 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15909]  in
                                      FStar_List.append bs_lhs uu____15900
                                       in
                                    copy_uvar u_lhs uu____15899 t_res_lhs wl2
                                     in
                                  (match uu____15892 with
                                   | (uu____15944,lhs',wl3) ->
                                       let uu____15947 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____15947 with
                                        | (uu____15964,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15841 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____15985 =
                                     let uu____15986 =
                                       let uu____15991 =
                                         let uu____15992 =
                                           let uu____15995 =
                                             let uu____16000 =
                                               let uu____16001 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16001]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16000
                                              in
                                           uu____15995
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____15992
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____15991)  in
                                     TERM uu____15986  in
                                   [uu____15985]  in
                                 let uu____16026 =
                                   let uu____16033 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16033 with
                                   | (p1,wl3) ->
                                       let uu____16053 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16053 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16026 with
                                  | (sub_probs,wl3) ->
                                      let uu____16085 =
                                        let uu____16086 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16086  in
                                      solve env1 uu____16085))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16120 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16120 with
                | (uu____16138,args) ->
                    (match args with | [] -> false | uu____16174 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16193 =
                  let uu____16194 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16194.FStar_Syntax_Syntax.n  in
                match uu____16193 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16198 -> true
                | uu____16214 -> false  in
              let uu____16216 = quasi_pattern env1 lhs1  in
              match uu____16216 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16234  ->
                         let uu____16235 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16235)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16244 = is_app rhs1  in
                  if uu____16244
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16249 = is_arrow rhs1  in
                     if uu____16249
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16261  ->
                               let uu____16262 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16262)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16266 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16266
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16272 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16272
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16277 = lhs  in
                (match uu____16277 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16281 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16281 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16299 =
                              let uu____16303 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16303
                               in
                            FStar_All.pipe_right uu____16299
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16324 = occurs_check ctx_uv rhs1  in
                          (match uu____16324 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16353 =
                                   let uu____16354 =
                                     let uu____16356 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16356
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16354
                                    in
                                 giveup_or_defer env orig wl uu____16353
                               else
                                 (let uu____16364 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16364
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16371 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16371
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16384  ->
                                              let uu____16385 =
                                                names_to_string1 fvs2  in
                                              let uu____16387 =
                                                names_to_string1 fvs1  in
                                              let uu____16389 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16385 uu____16387
                                                uu____16389)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16401 ->
                          if wl.defer_ok
                          then
                            let uu____16405 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16405
                          else
                            (let uu____16410 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16410 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16436 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16436
                             | (FStar_Util.Inl msg,uu____16438) ->
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
                then
                  let uu____16456 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16456
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16462 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16462
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16484 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16484
                else
                  (let uu____16489 =
                     let uu____16506 = quasi_pattern env lhs  in
                     let uu____16513 = quasi_pattern env rhs  in
                     (uu____16506, uu____16513)  in
                   match uu____16489 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16556 = lhs  in
                       (match uu____16556 with
                        | ({ FStar_Syntax_Syntax.n = uu____16557;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16559;_},u_lhs,uu____16561)
                            ->
                            let uu____16564 = rhs  in
                            (match uu____16564 with
                             | (uu____16565,u_rhs,uu____16567) ->
                                 let uu____16568 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16568
                                 then
                                   let uu____16575 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16575
                                 else
                                   (let uu____16578 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16578 with
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
                                        let uu____16610 =
                                          let uu____16617 =
                                            let uu____16620 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16620
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16617
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16610 with
                                         | (uu____16632,w,wl1) ->
                                             let w_app =
                                               let uu____16638 =
                                                 let uu____16643 =
                                                   FStar_List.map
                                                     (fun uu____16654  ->
                                                        match uu____16654
                                                        with
                                                        | (z,uu____16662) ->
                                                            let uu____16667 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16667) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16643
                                                  in
                                               uu____16638
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16669 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16669
                                               then
                                                 let uu____16674 =
                                                   let uu____16678 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16680 =
                                                     let uu____16684 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16686 =
                                                       let uu____16690 =
                                                         term_to_string w  in
                                                       let uu____16692 =
                                                         let uu____16696 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16705 =
                                                           let uu____16709 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16718 =
                                                             let uu____16722
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16722]
                                                              in
                                                           uu____16709 ::
                                                             uu____16718
                                                            in
                                                         uu____16696 ::
                                                           uu____16705
                                                          in
                                                       uu____16690 ::
                                                         uu____16692
                                                        in
                                                     uu____16684 ::
                                                       uu____16686
                                                      in
                                                   uu____16678 :: uu____16680
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16674
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16739 =
                                                     let uu____16744 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16744)  in
                                                   TERM uu____16739  in
                                                 let uu____16745 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16745
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16753 =
                                                        let uu____16758 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16758)
                                                         in
                                                      TERM uu____16753  in
                                                    [s1; s2])
                                                  in
                                               let uu____16759 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16759))))))
                   | uu____16760 ->
                       let uu____16777 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16777)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16831 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16831
            then
              let uu____16836 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16838 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16840 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16842 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16836 uu____16838 uu____16840 uu____16842
            else ());
           (let uu____16853 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16853 with
            | (head1,args1) ->
                let uu____16896 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16896 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16966 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____16966 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____16971 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____16971)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16992 =
                         FStar_Thunk.mk
                           (fun uu____16999  ->
                              let uu____17000 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17002 = args_to_string args1  in
                              let uu____17006 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17008 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17000 uu____17002 uu____17006
                                uu____17008)
                          in
                       giveup env1 uu____16992 orig
                     else
                       (let uu____17015 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17020 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17020 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17015
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2503_17024 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2503_17024.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2503_17024.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2503_17024.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2503_17024.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2503_17024.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2503_17024.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2503_17024.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2503_17024.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17034 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17034
                                    else solve env1 wl2))
                        else
                          (let uu____17039 = base_and_refinement env1 t1  in
                           match uu____17039 with
                           | (base1,refinement1) ->
                               let uu____17064 = base_and_refinement env1 t2
                                  in
                               (match uu____17064 with
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
                                           let uu____17229 =
                                             FStar_List.fold_right
                                               (fun uu____17269  ->
                                                  fun uu____17270  ->
                                                    match (uu____17269,
                                                            uu____17270)
                                                    with
                                                    | (((a1,uu____17322),
                                                        (a2,uu____17324)),
                                                       (probs,wl3)) ->
                                                        let uu____17373 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17373
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17229 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17416 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17416
                                                 then
                                                   let uu____17421 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17421
                                                 else ());
                                                (let uu____17427 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17427
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
                                                    (let uu____17454 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17454 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17470 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17470
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17478 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17478))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17503 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17503 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17519 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17519
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17527 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17527)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17555 =
                                           match uu____17555 with
                                           | (prob,reason) ->
                                               ((let uu____17572 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17572
                                                 then
                                                   let uu____17577 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17579 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17581 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17577 uu____17579
                                                     uu____17581
                                                 else ());
                                                (let uu____17587 =
                                                   let uu____17596 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17599 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17596, uu____17599)
                                                    in
                                                 match uu____17587 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17612 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17612 with
                                                      | (head1',uu____17630)
                                                          ->
                                                          let uu____17655 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17655
                                                           with
                                                           | (head2',uu____17673)
                                                               ->
                                                               let uu____17698
                                                                 =
                                                                 let uu____17703
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17704
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17703,
                                                                   uu____17704)
                                                                  in
                                                               (match uu____17698
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17706
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17706
                                                                    then
                                                                    let uu____17711
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17713
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17715
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17717
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17711
                                                                    uu____17713
                                                                    uu____17715
                                                                    uu____17717
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17722
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2591_17730
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2591_17730.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17732
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17732
                                                                    then
                                                                    let uu____17737
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17737
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17742 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17754 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17754 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17762 =
                                             let uu____17763 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17763.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17762 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17768 -> false  in
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
                                          | uu____17771 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17774 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2611_17810 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2611_17810.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2611_17810.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2611_17810.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2611_17810.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2611_17810.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2611_17810.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2611_17810.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2611_17810.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17886 = destruct_flex_t scrutinee wl1  in
             match uu____17886 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17897 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17897 with
                  | (xs,pat_term,uu____17913,uu____17914) ->
                      let uu____17919 =
                        FStar_List.fold_left
                          (fun uu____17942  ->
                             fun x  ->
                               match uu____17942 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____17963 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____17963 with
                                    | (uu____17982,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17919 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18003 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18003 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2651_18020 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2651_18020.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2651_18020.umax_heuristic_ok);
                                    tcenv = (uu___2651_18020.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18031 = solve env1 wl'  in
                                (match uu____18031 with
                                 | Success (uu____18034,imps) ->
                                     let wl'1 =
                                       let uu___2659_18037 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2659_18037.wl_deferred);
                                         ctr = (uu___2659_18037.ctr);
                                         defer_ok =
                                           (uu___2659_18037.defer_ok);
                                         smt_ok = (uu___2659_18037.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2659_18037.umax_heuristic_ok);
                                         tcenv = (uu___2659_18037.tcenv);
                                         wl_implicits =
                                           (uu___2659_18037.wl_implicits)
                                       }  in
                                     let uu____18038 = solve env1 wl'1  in
                                     (match uu____18038 with
                                      | Success (uu____18041,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2667_18045 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2667_18045.attempting);
                                                 wl_deferred =
                                                   (uu___2667_18045.wl_deferred);
                                                 ctr = (uu___2667_18045.ctr);
                                                 defer_ok =
                                                   (uu___2667_18045.defer_ok);
                                                 smt_ok =
                                                   (uu___2667_18045.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2667_18045.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2667_18045.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18046 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18052 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18075 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18075
                 then
                   let uu____18080 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18082 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18080 uu____18082
                 else ());
                (let uu____18087 =
                   let uu____18108 =
                     let uu____18117 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18117)  in
                   let uu____18124 =
                     let uu____18133 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18133)  in
                   (uu____18108, uu____18124)  in
                 match uu____18087 with
                 | ((uu____18163,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18166;
                                   FStar_Syntax_Syntax.vars = uu____18167;_}),
                    (s,t)) ->
                     let uu____18238 =
                       let uu____18240 = is_flex scrutinee  in
                       Prims.op_Negation uu____18240  in
                     if uu____18238
                     then
                       ((let uu____18251 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18251
                         then
                           let uu____18256 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18256
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18275 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18275
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18290 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18290
                           then
                             let uu____18295 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18297 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18295 uu____18297
                           else ());
                          (let pat_discriminates uu___28_18322 =
                             match uu___28_18322 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18338;
                                  FStar_Syntax_Syntax.p = uu____18339;_},FStar_Pervasives_Native.None
                                ,uu____18340) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18354;
                                  FStar_Syntax_Syntax.p = uu____18355;_},FStar_Pervasives_Native.None
                                ,uu____18356) -> true
                             | uu____18383 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18486 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18486 with
                                       | (uu____18488,uu____18489,t') ->
                                           let uu____18507 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18507 with
                                            | (FullMatch ,uu____18519) ->
                                                true
                                            | (HeadMatch
                                               uu____18533,uu____18534) ->
                                                true
                                            | uu____18549 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18586 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18586
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18597 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18597 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18685,uu____18686) ->
                                       branches1
                                   | uu____18831 -> branches  in
                                 let uu____18886 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18895 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18895 with
                                        | (p,uu____18899,uu____18900) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _18929  -> FStar_Util.Inr _18929)
                                   uu____18886))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18959 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____18959 with
                                | (p,uu____18968,e) ->
                                    ((let uu____18987 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____18987
                                      then
                                        let uu____18992 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____18994 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18992 uu____18994
                                      else ());
                                     (let uu____18999 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19014  -> FStar_Util.Inr _19014)
                                        uu____18999)))))
                 | ((s,t),(uu____19017,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19020;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19021;_}))
                     ->
                     let uu____19090 =
                       let uu____19092 = is_flex scrutinee  in
                       Prims.op_Negation uu____19092  in
                     if uu____19090
                     then
                       ((let uu____19103 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19103
                         then
                           let uu____19108 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19108
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19127 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19127
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19142 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19142
                           then
                             let uu____19147 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19149 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19147 uu____19149
                           else ());
                          (let pat_discriminates uu___28_19174 =
                             match uu___28_19174 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19190;
                                  FStar_Syntax_Syntax.p = uu____19191;_},FStar_Pervasives_Native.None
                                ,uu____19192) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19206;
                                  FStar_Syntax_Syntax.p = uu____19207;_},FStar_Pervasives_Native.None
                                ,uu____19208) -> true
                             | uu____19235 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19338 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19338 with
                                       | (uu____19340,uu____19341,t') ->
                                           let uu____19359 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19359 with
                                            | (FullMatch ,uu____19371) ->
                                                true
                                            | (HeadMatch
                                               uu____19385,uu____19386) ->
                                                true
                                            | uu____19401 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19438 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19438
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19449 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19449 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19537,uu____19538) ->
                                       branches1
                                   | uu____19683 -> branches  in
                                 let uu____19738 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19747 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19747 with
                                        | (p,uu____19751,uu____19752) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19781  -> FStar_Util.Inr _19781)
                                   uu____19738))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19811 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19811 with
                                | (p,uu____19820,e) ->
                                    ((let uu____19839 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19839
                                      then
                                        let uu____19844 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19846 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19844 uu____19846
                                      else ());
                                     (let uu____19851 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19866  -> FStar_Util.Inr _19866)
                                        uu____19851)))))
                 | uu____19867 ->
                     ((let uu____19889 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19889
                       then
                         let uu____19894 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19896 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19894 uu____19896
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19942 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19942
            then
              let uu____19947 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____19949 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____19951 = FStar_Syntax_Print.term_to_string t1  in
              let uu____19953 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19947 uu____19949 uu____19951 uu____19953
            else ());
           (let uu____19958 = head_matches_delta env1 wl1 t1 t2  in
            match uu____19958 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____19989,uu____19990) ->
                     let rec may_relate head3 =
                       let uu____20018 =
                         let uu____20019 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20019.FStar_Syntax_Syntax.n  in
                       match uu____20018 with
                       | FStar_Syntax_Syntax.Tm_name uu____20023 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20025 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20050 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20050 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20052 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20055
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20056 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20059,uu____20060) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20102) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20108) ->
                           may_relate t
                       | uu____20113 -> false  in
                     let uu____20115 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20115 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20128 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20128
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20138 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20138
                          then
                            let uu____20141 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20141 with
                             | (guard,wl2) ->
                                 let uu____20148 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20148)
                          else
                            (let uu____20151 =
                               FStar_Thunk.mk
                                 (fun uu____20158  ->
                                    let uu____20159 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20161 =
                                      let uu____20163 =
                                        let uu____20167 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20167
                                          (fun x  ->
                                             let uu____20174 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20174)
                                         in
                                      FStar_Util.dflt "" uu____20163  in
                                    let uu____20179 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20181 =
                                      let uu____20183 =
                                        let uu____20187 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20187
                                          (fun x  ->
                                             let uu____20194 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20194)
                                         in
                                      FStar_Util.dflt "" uu____20183  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20159 uu____20161 uu____20179
                                      uu____20181)
                                in
                             giveup env1 uu____20151 orig))
                 | (HeadMatch (true ),uu____20200) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20215 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20215 with
                        | (guard,wl2) ->
                            let uu____20222 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20222)
                     else
                       (let uu____20225 =
                          FStar_Thunk.mk
                            (fun uu____20230  ->
                               let uu____20231 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20233 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20231 uu____20233)
                           in
                        giveup env1 uu____20225 orig)
                 | (uu____20236,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2842_20250 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2842_20250.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2842_20250.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2842_20250.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2842_20250.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2842_20250.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2842_20250.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2842_20250.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2842_20250.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20277 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20277
          then
            let uu____20280 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20280
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20286 =
                let uu____20289 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20289  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20286 t1);
             (let uu____20308 =
                let uu____20311 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20311  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20308 t2);
             (let uu____20330 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20330
              then
                let uu____20334 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20336 =
                  let uu____20338 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20340 =
                    let uu____20342 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20342  in
                  Prims.op_Hat uu____20338 uu____20340  in
                let uu____20345 =
                  let uu____20347 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20349 =
                    let uu____20351 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20351  in
                  Prims.op_Hat uu____20347 uu____20349  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20334 uu____20336 uu____20345
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20358,uu____20359) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20375,FStar_Syntax_Syntax.Tm_delayed uu____20376) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20392,uu____20393) ->
                  let uu____20420 =
                    let uu___2873_20421 = problem  in
                    let uu____20422 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2873_20421.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20422;
                      FStar_TypeChecker_Common.relation =
                        (uu___2873_20421.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2873_20421.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2873_20421.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2873_20421.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2873_20421.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2873_20421.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2873_20421.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2873_20421.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20420 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20423,uu____20424) ->
                  let uu____20431 =
                    let uu___2879_20432 = problem  in
                    let uu____20433 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2879_20432.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20433;
                      FStar_TypeChecker_Common.relation =
                        (uu___2879_20432.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2879_20432.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2879_20432.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2879_20432.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2879_20432.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2879_20432.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2879_20432.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2879_20432.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20431 wl
              | (uu____20434,FStar_Syntax_Syntax.Tm_ascribed uu____20435) ->
                  let uu____20462 =
                    let uu___2885_20463 = problem  in
                    let uu____20464 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2885_20463.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2885_20463.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2885_20463.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20464;
                      FStar_TypeChecker_Common.element =
                        (uu___2885_20463.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2885_20463.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2885_20463.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2885_20463.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2885_20463.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2885_20463.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20462 wl
              | (uu____20465,FStar_Syntax_Syntax.Tm_meta uu____20466) ->
                  let uu____20473 =
                    let uu___2891_20474 = problem  in
                    let uu____20475 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2891_20474.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2891_20474.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2891_20474.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20475;
                      FStar_TypeChecker_Common.element =
                        (uu___2891_20474.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2891_20474.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2891_20474.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2891_20474.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2891_20474.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2891_20474.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20473 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20477),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20479)) ->
                  let uu____20488 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20488
              | (FStar_Syntax_Syntax.Tm_bvar uu____20489,uu____20490) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20492,FStar_Syntax_Syntax.Tm_bvar uu____20493) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20563 =
                    match uu___29_20563 with
                    | [] -> c
                    | bs ->
                        let uu____20591 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20591
                     in
                  let uu____20602 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20602 with
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
                                    let uu____20751 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20751
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
                  let mk_t t l uu___30_20840 =
                    match uu___30_20840 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20882 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20882 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21027 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21028 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21027
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21028 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21030,uu____21031) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21062 -> true
                    | uu____21082 -> false  in
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
                      (let uu____21142 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21150 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21150.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21150.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21150.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21150.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21150.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21150.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21150.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21150.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21150.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21150.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21150.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21150.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21150.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21150.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21150.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21150.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21150.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21150.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21150.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21150.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21150.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21150.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21150.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21150.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21150.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21150.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21150.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21150.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21150.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21150.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21150.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21150.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21150.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21150.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21150.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21150.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21150.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21150.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21150.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21150.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21150.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21150.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21150.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21150.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21142 with
                       | (uu____21155,ty,uu____21157) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21166 =
                                 let uu____21167 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21167.FStar_Syntax_Syntax.n  in
                               match uu____21166 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21170 ->
                                   let uu____21177 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21177
                               | uu____21178 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21181 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21181
                             then
                               let uu____21186 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21188 =
                                 let uu____21190 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21190
                                  in
                               let uu____21191 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21186 uu____21188 uu____21191
                             else ());
                            r1))
                     in
                  let uu____21196 =
                    let uu____21213 = maybe_eta t1  in
                    let uu____21220 = maybe_eta t2  in
                    (uu____21213, uu____21220)  in
                  (match uu____21196 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21262 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21262.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21262.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21262.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21262.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21262.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21262.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21262.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21262.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21283 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21283
                       then
                         let uu____21286 = destruct_flex_t not_abs wl  in
                         (match uu____21286 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21303 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21303.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21303.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21303.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21303.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21303.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21303.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21303.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21303.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21306 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21306 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21329 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21329
                       then
                         let uu____21332 = destruct_flex_t not_abs wl  in
                         (match uu____21332 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21349 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21349.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21349.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21349.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21349.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21349.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21349.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21349.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21349.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21352 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21352 orig))
                   | uu____21355 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21373,FStar_Syntax_Syntax.Tm_abs uu____21374) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21405 -> true
                    | uu____21425 -> false  in
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
                      (let uu____21485 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2993_21493 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2993_21493.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2993_21493.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2993_21493.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2993_21493.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2993_21493.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2993_21493.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2993_21493.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2993_21493.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2993_21493.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2993_21493.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2993_21493.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2993_21493.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2993_21493.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2993_21493.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2993_21493.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2993_21493.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2993_21493.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2993_21493.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2993_21493.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2993_21493.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2993_21493.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2993_21493.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2993_21493.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2993_21493.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2993_21493.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2993_21493.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2993_21493.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2993_21493.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2993_21493.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2993_21493.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2993_21493.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2993_21493.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2993_21493.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2993_21493.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2993_21493.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2993_21493.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2993_21493.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2993_21493.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2993_21493.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2993_21493.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2993_21493.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2993_21493.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2993_21493.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2993_21493.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21485 with
                       | (uu____21498,ty,uu____21500) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21509 =
                                 let uu____21510 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21510.FStar_Syntax_Syntax.n  in
                               match uu____21509 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21513 ->
                                   let uu____21520 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21520
                               | uu____21521 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21524 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21524
                             then
                               let uu____21529 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21531 =
                                 let uu____21533 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21533
                                  in
                               let uu____21534 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21529 uu____21531 uu____21534
                             else ());
                            r1))
                     in
                  let uu____21539 =
                    let uu____21556 = maybe_eta t1  in
                    let uu____21563 = maybe_eta t2  in
                    (uu____21556, uu____21563)  in
                  (match uu____21539 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3014_21605 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3014_21605.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3014_21605.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3014_21605.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3014_21605.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3014_21605.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3014_21605.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3014_21605.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3014_21605.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21626 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21626
                       then
                         let uu____21629 = destruct_flex_t not_abs wl  in
                         (match uu____21629 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21646 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21646.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21646.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21646.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21646.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21646.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21646.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21646.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21646.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21649 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21649 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21672 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21672
                       then
                         let uu____21675 = destruct_flex_t not_abs wl  in
                         (match uu____21675 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3031_21692 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3031_21692.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3031_21692.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3031_21692.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3031_21692.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3031_21692.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3031_21692.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3031_21692.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3031_21692.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21695 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21695 orig))
                   | uu____21698 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21728 =
                    let uu____21733 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21733 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3054_21761 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21761.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21761.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21763 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21763.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21763.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21764,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3054_21779 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3054_21779.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3054_21779.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3056_21781 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3056_21781.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3056_21781.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21782 -> (x1, x2)  in
                  (match uu____21728 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21801 = as_refinement false env t11  in
                       (match uu____21801 with
                        | (x12,phi11) ->
                            let uu____21809 = as_refinement false env t21  in
                            (match uu____21809 with
                             | (x22,phi21) ->
                                 ((let uu____21818 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21818
                                   then
                                     ((let uu____21823 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21825 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21827 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21823
                                         uu____21825 uu____21827);
                                      (let uu____21830 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21832 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21834 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21830
                                         uu____21832 uu____21834))
                                   else ());
                                  (let uu____21839 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21839 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
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
                                         let uu____21910 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21910
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21922 =
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
                                         (let uu____21935 =
                                            let uu____21938 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21938
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21935
                                            (p_guard base_prob));
                                         (let uu____21957 =
                                            let uu____21960 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21960
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____21957
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____21979 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____21979)
                                          in
                                       let has_uvars =
                                         (let uu____21984 =
                                            let uu____21986 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____21986
                                             in
                                          Prims.op_Negation uu____21984) ||
                                           (let uu____21990 =
                                              let uu____21992 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____21992
                                               in
                                            Prims.op_Negation uu____21990)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____21996 =
                                           let uu____22001 =
                                             let uu____22010 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22010]  in
                                           mk_t_problem wl1 uu____22001 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____21996 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22033 =
                                                solve env1
                                                  (let uu___3099_22035 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3099_22035.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3099_22035.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3099_22035.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3099_22035.tcenv);
                                                     wl_implicits =
                                                       (uu___3099_22035.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22033 with
                                               | Failed (prob,msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    if
                                                      ((Prims.op_Negation
                                                          env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                         && has_uvars)
                                                        ||
                                                        (Prims.op_Negation
                                                           wl2.smt_ok)
                                                    then giveup env1 msg prob
                                                    else fallback ())
                                               | Success uu____22050 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22059 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22059
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3112_22068 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3112_22068.attempting);
                                                         wl_deferred =
                                                           (uu___3112_22068.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3112_22068.defer_ok);
                                                         smt_ok =
                                                           (uu___3112_22068.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3112_22068.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3112_22068.tcenv);
                                                         wl_implicits =
                                                           (uu___3112_22068.wl_implicits)
                                                       }  in
                                                     let uu____22070 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22070))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22073,FStar_Syntax_Syntax.Tm_uvar uu____22074) ->
                  let uu____22099 = destruct_flex_t t1 wl  in
                  (match uu____22099 with
                   | (f1,wl1) ->
                       let uu____22106 = destruct_flex_t t2 wl1  in
                       (match uu____22106 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22113;
                    FStar_Syntax_Syntax.pos = uu____22114;
                    FStar_Syntax_Syntax.vars = uu____22115;_},uu____22116),FStar_Syntax_Syntax.Tm_uvar
                 uu____22117) ->
                  let uu____22166 = destruct_flex_t t1 wl  in
                  (match uu____22166 with
                   | (f1,wl1) ->
                       let uu____22173 = destruct_flex_t t2 wl1  in
                       (match uu____22173 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22180,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22181;
                    FStar_Syntax_Syntax.pos = uu____22182;
                    FStar_Syntax_Syntax.vars = uu____22183;_},uu____22184))
                  ->
                  let uu____22233 = destruct_flex_t t1 wl  in
                  (match uu____22233 with
                   | (f1,wl1) ->
                       let uu____22240 = destruct_flex_t t2 wl1  in
                       (match uu____22240 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22247;
                    FStar_Syntax_Syntax.pos = uu____22248;
                    FStar_Syntax_Syntax.vars = uu____22249;_},uu____22250),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22251;
                    FStar_Syntax_Syntax.pos = uu____22252;
                    FStar_Syntax_Syntax.vars = uu____22253;_},uu____22254))
                  ->
                  let uu____22327 = destruct_flex_t t1 wl  in
                  (match uu____22327 with
                   | (f1,wl1) ->
                       let uu____22334 = destruct_flex_t t2 wl1  in
                       (match uu____22334 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22341,uu____22342) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22355 = destruct_flex_t t1 wl  in
                  (match uu____22355 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22362;
                    FStar_Syntax_Syntax.pos = uu____22363;
                    FStar_Syntax_Syntax.vars = uu____22364;_},uu____22365),uu____22366)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22403 = destruct_flex_t t1 wl  in
                  (match uu____22403 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22410,FStar_Syntax_Syntax.Tm_uvar uu____22411) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22424,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22425;
                    FStar_Syntax_Syntax.pos = uu____22426;
                    FStar_Syntax_Syntax.vars = uu____22427;_},uu____22428))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22465,FStar_Syntax_Syntax.Tm_arrow uu____22466) ->
                  solve_t' env
                    (let uu___3212_22494 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22494.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22494.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22494.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22494.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22494.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22494.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22494.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22494.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22494.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22495;
                    FStar_Syntax_Syntax.pos = uu____22496;
                    FStar_Syntax_Syntax.vars = uu____22497;_},uu____22498),FStar_Syntax_Syntax.Tm_arrow
                 uu____22499) ->
                  solve_t' env
                    (let uu___3212_22551 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3212_22551.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3212_22551.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3212_22551.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3212_22551.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3212_22551.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3212_22551.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3212_22551.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3212_22551.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3212_22551.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22552,FStar_Syntax_Syntax.Tm_uvar uu____22553) ->
                  let uu____22566 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22566
              | (uu____22567,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22568;
                    FStar_Syntax_Syntax.pos = uu____22569;
                    FStar_Syntax_Syntax.vars = uu____22570;_},uu____22571))
                  ->
                  let uu____22608 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22608
              | (FStar_Syntax_Syntax.Tm_uvar uu____22609,uu____22610) ->
                  let uu____22623 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22623
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22624;
                    FStar_Syntax_Syntax.pos = uu____22625;
                    FStar_Syntax_Syntax.vars = uu____22626;_},uu____22627),uu____22628)
                  ->
                  let uu____22665 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22665
              | (FStar_Syntax_Syntax.Tm_refine uu____22666,uu____22667) ->
                  let t21 =
                    let uu____22675 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22675  in
                  solve_t env
                    (let uu___3247_22701 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3247_22701.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3247_22701.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3247_22701.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3247_22701.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3247_22701.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3247_22701.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3247_22701.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3247_22701.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3247_22701.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22702,FStar_Syntax_Syntax.Tm_refine uu____22703) ->
                  let t11 =
                    let uu____22711 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22711  in
                  solve_t env
                    (let uu___3254_22737 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22737.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22737.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3254_22737.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22737.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22737.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22737.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22737.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22737.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22737.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22819 =
                    let uu____22820 = guard_of_prob env wl problem t1 t2  in
                    match uu____22820 with
                    | (guard,wl1) ->
                        let uu____22827 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22827
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23046 = br1  in
                        (match uu____23046 with
                         | (p1,w1,uu____23075) ->
                             let uu____23092 = br2  in
                             (match uu____23092 with
                              | (p2,w2,uu____23115) ->
                                  let uu____23120 =
                                    let uu____23122 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23122  in
                                  if uu____23120
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23149 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23149 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23186 = br2  in
                                         (match uu____23186 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23219 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23219
                                                 in
                                              let uu____23224 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23255,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23276) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23335 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23335 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23224
                                                (fun uu____23407  ->
                                                   match uu____23407 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23444 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23444
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23465
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23465
                                                              then
                                                                let uu____23470
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23472
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23470
                                                                  uu____23472
                                                              else ());
                                                             (let uu____23478
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23478
                                                                (fun
                                                                   uu____23514
                                                                    ->
                                                                   match uu____23514
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
                    | uu____23643 -> FStar_Pervasives_Native.None  in
                  let uu____23684 = solve_branches wl brs1 brs2  in
                  (match uu____23684 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23710 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23710 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23737 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23737 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23771 =
                                FStar_List.map
                                  (fun uu____23783  ->
                                     match uu____23783 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23771  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23792 =
                              let uu____23793 =
                                let uu____23794 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23794
                                  (let uu___3353_23802 = wl3  in
                                   {
                                     attempting =
                                       (uu___3353_23802.attempting);
                                     wl_deferred =
                                       (uu___3353_23802.wl_deferred);
                                     ctr = (uu___3353_23802.ctr);
                                     defer_ok = (uu___3353_23802.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3353_23802.umax_heuristic_ok);
                                     tcenv = (uu___3353_23802.tcenv);
                                     wl_implicits =
                                       (uu___3353_23802.wl_implicits)
                                   })
                                 in
                              solve env uu____23793  in
                            (match uu____23792 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23807 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23816 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23816 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23819,uu____23820) ->
                  let head1 =
                    let uu____23844 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23844
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23890 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23890
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23936 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23936
                    then
                      let uu____23940 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23942 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23944 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23940 uu____23942 uu____23944
                    else ());
                   (let no_free_uvars t =
                      (let uu____23958 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23958) &&
                        (let uu____23962 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23962)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23981 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23981 = FStar_Syntax_Util.Equal  in
                    let uu____23982 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23982
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23986 = equal t1 t2  in
                         (if uu____23986
                          then
                            let uu____23989 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23989
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23994 =
                            let uu____24001 = equal t1 t2  in
                            if uu____24001
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24014 = mk_eq2 wl env orig t1 t2  in
                               match uu____24014 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23994 with
                          | (guard,wl1) ->
                              let uu____24035 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24035))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24038,uu____24039) ->
                  let head1 =
                    let uu____24047 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24047
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24093 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24093
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24139 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24139
                    then
                      let uu____24143 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24145 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24147 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24143 uu____24145 uu____24147
                    else ());
                   (let no_free_uvars t =
                      (let uu____24161 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24161) &&
                        (let uu____24165 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24165)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24184 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24184 = FStar_Syntax_Util.Equal  in
                    let uu____24185 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24185
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24189 = equal t1 t2  in
                         (if uu____24189
                          then
                            let uu____24192 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24192
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24197 =
                            let uu____24204 = equal t1 t2  in
                            if uu____24204
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24217 = mk_eq2 wl env orig t1 t2  in
                               match uu____24217 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24197 with
                          | (guard,wl1) ->
                              let uu____24238 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24238))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24241,uu____24242) ->
                  let head1 =
                    let uu____24244 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24244
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24290 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24290
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24336 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24336
                    then
                      let uu____24340 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24342 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24344 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24340 uu____24342 uu____24344
                    else ());
                   (let no_free_uvars t =
                      (let uu____24358 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24358) &&
                        (let uu____24362 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24362)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24381 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24381 = FStar_Syntax_Util.Equal  in
                    let uu____24382 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24382
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24386 = equal t1 t2  in
                         (if uu____24386
                          then
                            let uu____24389 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24389
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24394 =
                            let uu____24401 = equal t1 t2  in
                            if uu____24401
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24414 = mk_eq2 wl env orig t1 t2  in
                               match uu____24414 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24394 with
                          | (guard,wl1) ->
                              let uu____24435 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24435))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24438,uu____24439) ->
                  let head1 =
                    let uu____24441 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24441
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24487 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24487
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24533 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24533
                    then
                      let uu____24537 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24539 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24541 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24537 uu____24539 uu____24541
                    else ());
                   (let no_free_uvars t =
                      (let uu____24555 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24555) &&
                        (let uu____24559 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24559)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24578 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24578 = FStar_Syntax_Util.Equal  in
                    let uu____24579 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24579
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24583 = equal t1 t2  in
                         (if uu____24583
                          then
                            let uu____24586 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24586
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24591 =
                            let uu____24598 = equal t1 t2  in
                            if uu____24598
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24611 = mk_eq2 wl env orig t1 t2  in
                               match uu____24611 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24591 with
                          | (guard,wl1) ->
                              let uu____24632 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24632))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24635,uu____24636) ->
                  let head1 =
                    let uu____24638 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24638
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24684 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24684
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24730 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24730
                    then
                      let uu____24734 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24736 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24738 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24734 uu____24736 uu____24738
                    else ());
                   (let no_free_uvars t =
                      (let uu____24752 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24752) &&
                        (let uu____24756 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24756)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24775 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24775 = FStar_Syntax_Util.Equal  in
                    let uu____24776 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24776
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24780 = equal t1 t2  in
                         (if uu____24780
                          then
                            let uu____24783 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24783
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24788 =
                            let uu____24795 = equal t1 t2  in
                            if uu____24795
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24808 = mk_eq2 wl env orig t1 t2  in
                               match uu____24808 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24788 with
                          | (guard,wl1) ->
                              let uu____24829 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24829))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24832,uu____24833) ->
                  let head1 =
                    let uu____24851 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24851
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24897 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24897
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24943 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24943
                    then
                      let uu____24947 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24949 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24951 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24947 uu____24949 uu____24951
                    else ());
                   (let no_free_uvars t =
                      (let uu____24965 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24965) &&
                        (let uu____24969 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24969)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24988 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24988 = FStar_Syntax_Util.Equal  in
                    let uu____24989 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24989
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24993 = equal t1 t2  in
                         (if uu____24993
                          then
                            let uu____24996 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24996
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25001 =
                            let uu____25008 = equal t1 t2  in
                            if uu____25008
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25021 = mk_eq2 wl env orig t1 t2  in
                               match uu____25021 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25001 with
                          | (guard,wl1) ->
                              let uu____25042 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25042))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25045,FStar_Syntax_Syntax.Tm_match uu____25046) ->
                  let head1 =
                    let uu____25070 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25070
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25116 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25116
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25162 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25162
                    then
                      let uu____25166 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25168 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25170 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25166 uu____25168 uu____25170
                    else ());
                   (let no_free_uvars t =
                      (let uu____25184 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25184) &&
                        (let uu____25188 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25188)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25207 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25207 = FStar_Syntax_Util.Equal  in
                    let uu____25208 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25208
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25212 = equal t1 t2  in
                         (if uu____25212
                          then
                            let uu____25215 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25215
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25220 =
                            let uu____25227 = equal t1 t2  in
                            if uu____25227
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25240 = mk_eq2 wl env orig t1 t2  in
                               match uu____25240 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25220 with
                          | (guard,wl1) ->
                              let uu____25261 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25261))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25264,FStar_Syntax_Syntax.Tm_uinst uu____25265) ->
                  let head1 =
                    let uu____25273 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25273
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25319 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25319
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25365 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25365
                    then
                      let uu____25369 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25371 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25373 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25369 uu____25371 uu____25373
                    else ());
                   (let no_free_uvars t =
                      (let uu____25387 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25387) &&
                        (let uu____25391 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25391)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25410 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25410 = FStar_Syntax_Util.Equal  in
                    let uu____25411 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25411
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25415 = equal t1 t2  in
                         (if uu____25415
                          then
                            let uu____25418 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25418
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25423 =
                            let uu____25430 = equal t1 t2  in
                            if uu____25430
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25443 = mk_eq2 wl env orig t1 t2  in
                               match uu____25443 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25423 with
                          | (guard,wl1) ->
                              let uu____25464 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25464))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25467,FStar_Syntax_Syntax.Tm_name uu____25468) ->
                  let head1 =
                    let uu____25470 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25470
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25516 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25516
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25556 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25556
                    then
                      let uu____25560 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25562 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25564 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25560 uu____25562 uu____25564
                    else ());
                   (let no_free_uvars t =
                      (let uu____25578 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25578) &&
                        (let uu____25582 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25582)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25601 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25601 = FStar_Syntax_Util.Equal  in
                    let uu____25602 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25602
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25606 = equal t1 t2  in
                         (if uu____25606
                          then
                            let uu____25609 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25609
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25614 =
                            let uu____25621 = equal t1 t2  in
                            if uu____25621
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25634 = mk_eq2 wl env orig t1 t2  in
                               match uu____25634 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25614 with
                          | (guard,wl1) ->
                              let uu____25655 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25655))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25658,FStar_Syntax_Syntax.Tm_constant uu____25659) ->
                  let head1 =
                    let uu____25661 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25661
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25701 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25701
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25741 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25741
                    then
                      let uu____25745 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25747 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25749 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25745 uu____25747 uu____25749
                    else ());
                   (let no_free_uvars t =
                      (let uu____25763 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25763) &&
                        (let uu____25767 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25767)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25786 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25786 = FStar_Syntax_Util.Equal  in
                    let uu____25787 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25787
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25791 = equal t1 t2  in
                         (if uu____25791
                          then
                            let uu____25794 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25794
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25799 =
                            let uu____25806 = equal t1 t2  in
                            if uu____25806
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25819 = mk_eq2 wl env orig t1 t2  in
                               match uu____25819 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25799 with
                          | (guard,wl1) ->
                              let uu____25840 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25840))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25843,FStar_Syntax_Syntax.Tm_fvar uu____25844) ->
                  let head1 =
                    let uu____25846 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25846
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25892 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25892
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25938 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25938
                    then
                      let uu____25942 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25944 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25946 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25942 uu____25944 uu____25946
                    else ());
                   (let no_free_uvars t =
                      (let uu____25960 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25960) &&
                        (let uu____25964 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25964)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25983 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25983 = FStar_Syntax_Util.Equal  in
                    let uu____25984 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25984
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25988 = equal t1 t2  in
                         (if uu____25988
                          then
                            let uu____25991 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25991
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25996 =
                            let uu____26003 = equal t1 t2  in
                            if uu____26003
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26016 = mk_eq2 wl env orig t1 t2  in
                               match uu____26016 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25996 with
                          | (guard,wl1) ->
                              let uu____26037 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26037))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26040,FStar_Syntax_Syntax.Tm_app uu____26041) ->
                  let head1 =
                    let uu____26059 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26059
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26099 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26099
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26139 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26139
                    then
                      let uu____26143 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26145 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26147 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26143 uu____26145 uu____26147
                    else ());
                   (let no_free_uvars t =
                      (let uu____26161 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26161) &&
                        (let uu____26165 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26165)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26184 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26184 = FStar_Syntax_Util.Equal  in
                    let uu____26185 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26185
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26189 = equal t1 t2  in
                         (if uu____26189
                          then
                            let uu____26192 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26192
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26197 =
                            let uu____26204 = equal t1 t2  in
                            if uu____26204
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26217 = mk_eq2 wl env orig t1 t2  in
                               match uu____26217 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26197 with
                          | (guard,wl1) ->
                              let uu____26238 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26238))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26241,FStar_Syntax_Syntax.Tm_let uu____26242) ->
                  let uu____26269 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26269
                  then
                    let uu____26272 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26272
                  else
                    (let uu____26275 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26275 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26278,uu____26279) ->
                  let uu____26293 =
                    let uu____26299 =
                      let uu____26301 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26303 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26305 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26307 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26301 uu____26303 uu____26305 uu____26307
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26299)
                     in
                  FStar_Errors.raise_error uu____26293
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26311,FStar_Syntax_Syntax.Tm_let uu____26312) ->
                  let uu____26326 =
                    let uu____26332 =
                      let uu____26334 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26336 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26338 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26340 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26334 uu____26336 uu____26338 uu____26340
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26332)
                     in
                  FStar_Errors.raise_error uu____26326
                    t1.FStar_Syntax_Syntax.pos
              | uu____26344 ->
                  let uu____26349 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26349 orig))))

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
        let solve_eq c1_comp c2_comp g_lift =
          (let uu____26415 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26415
           then
             let uu____26420 =
               let uu____26422 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26422  in
             let uu____26423 =
               let uu____26425 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26425  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26420 uu____26423
           else ());
          (let uu____26429 =
             let uu____26431 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26431  in
           if uu____26429
           then
             let uu____26434 =
               FStar_Thunk.mk
                 (fun uu____26439  ->
                    let uu____26440 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26442 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26440 uu____26442)
                in
             giveup env uu____26434 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26464 =
                  FStar_Thunk.mk
                    (fun uu____26469  ->
                       let uu____26470 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26472 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26470 uu____26472)
                   in
                giveup env uu____26464 orig)
             else
               (let uu____26477 =
                  FStar_List.fold_left2
                    (fun uu____26498  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26498 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26519 =
                                 let uu____26524 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26525 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26524
                                   FStar_TypeChecker_Common.EQ uu____26525
                                   "effect universes"
                                  in
                               (match uu____26519 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26477 with
                | (univ_sub_probs,wl1) ->
                    let uu____26545 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26545 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26553 =
                           FStar_List.fold_right2
                             (fun uu____26590  ->
                                fun uu____26591  ->
                                  fun uu____26592  ->
                                    match (uu____26590, uu____26591,
                                            uu____26592)
                                    with
                                    | ((a1,uu____26636),(a2,uu____26638),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26671 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26671 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26553 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26698 =
                                  let uu____26701 =
                                    let uu____26704 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26704
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26701
                                   in
                                FStar_List.append univ_sub_probs uu____26698
                                 in
                              let guard =
                                let guard =
                                  let uu____26726 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26726  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3505_26735 = wl3  in
                                {
                                  attempting = (uu___3505_26735.attempting);
                                  wl_deferred = (uu___3505_26735.wl_deferred);
                                  ctr = (uu___3505_26735.ctr);
                                  defer_ok = (uu___3505_26735.defer_ok);
                                  smt_ok = (uu___3505_26735.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3505_26735.umax_heuristic_ok);
                                  tcenv = (uu___3505_26735.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26737 = attempt sub_probs wl5  in
                              solve env uu____26737))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26755 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26755
           then
             let uu____26760 =
               let uu____26762 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26762
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26764 =
               let uu____26766 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26766
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26760 uu____26764
           else ());
          (let uu____26771 =
             let uu____26776 =
               let uu____26781 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26781
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26776
               (fun uu____26798  ->
                  match uu____26798 with
                  | (c,g) ->
                      let uu____26809 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26809, g))
              in
           match uu____26771 with
           | (c12,g_lift) ->
               ((let uu____26813 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26813
                 then
                   let uu____26818 =
                     let uu____26820 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26820
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26822 =
                     let uu____26824 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26824
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26818 uu____26822
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3525_26834 = wl  in
                     {
                       attempting = (uu___3525_26834.attempting);
                       wl_deferred = (uu___3525_26834.wl_deferred);
                       ctr = (uu___3525_26834.ctr);
                       defer_ok = (uu___3525_26834.defer_ok);
                       smt_ok = (uu___3525_26834.smt_ok);
                       umax_heuristic_ok =
                         (uu___3525_26834.umax_heuristic_ok);
                       tcenv = (uu___3525_26834.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26835 =
                     let rec is_uvar1 t =
                       let uu____26849 =
                         let uu____26850 = FStar_Syntax_Subst.compress t  in
                         uu____26850.FStar_Syntax_Syntax.n  in
                       match uu____26849 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26854 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26869) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26875) ->
                           is_uvar1 t1
                       | uu____26900 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26934  ->
                          fun uu____26935  ->
                            fun uu____26936  ->
                              match (uu____26934, uu____26935, uu____26936)
                              with
                              | ((a1,uu____26980),(a2,uu____26982),(is_sub_probs,wl2))
                                  ->
                                  let uu____27015 = is_uvar1 a1  in
                                  if uu____27015
                                  then
                                    ((let uu____27025 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27025
                                      then
                                        let uu____27030 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27032 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27030 uu____27032
                                      else ());
                                     (let uu____27037 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27037 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26835 with
                   | (is_sub_probs,wl2) ->
                       let uu____27065 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27065 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27073 =
                              let uu____27078 =
                                let uu____27079 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27079
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27078
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27073 with
                             | (uu____27086,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27097 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27099 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27097 s uu____27099
                                    in
                                 let uu____27102 =
                                   let uu____27131 =
                                     let uu____27132 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27132.FStar_Syntax_Syntax.n  in
                                   match uu____27131 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27192 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27192 with
                                        | (a::bs1,c3) ->
                                            let uu____27248 =
                                              let uu____27267 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27267
                                                (fun uu____27371  ->
                                                   match uu____27371 with
                                                   | (l1,l2) ->
                                                       let uu____27444 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27444))
                                               in
                                            (match uu____27248 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27549 ->
                                       let uu____27550 =
                                         let uu____27556 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27556)
                                          in
                                       FStar_Errors.raise_error uu____27550 r
                                    in
                                 (match uu____27102 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27632 =
                                        let uu____27639 =
                                          let uu____27640 =
                                            let uu____27641 =
                                              let uu____27648 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27648,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27641
                                             in
                                          [uu____27640]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27639
                                          (fun b  ->
                                             let uu____27664 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27666 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27668 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27664 uu____27666
                                               uu____27668) r
                                         in
                                      (match uu____27632 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27678 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27678
                                             then
                                               let uu____27683 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27692 =
                                                          let uu____27694 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27694
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27692) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27683
                                             else ());
                                            (let wl4 =
                                               let uu___3597_27702 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3597_27702.attempting);
                                                 wl_deferred =
                                                   (uu___3597_27702.wl_deferred);
                                                 ctr = (uu___3597_27702.ctr);
                                                 defer_ok =
                                                   (uu___3597_27702.defer_ok);
                                                 smt_ok =
                                                   (uu___3597_27702.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3597_27702.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3597_27702.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27727 =
                                                        let uu____27734 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27734, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27727) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27751 =
                                               let f_sort_is =
                                                 let uu____27761 =
                                                   let uu____27762 =
                                                     let uu____27765 =
                                                       let uu____27766 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27766.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27765
                                                      in
                                                   uu____27762.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27761 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27777,uu____27778::is)
                                                     ->
                                                     let uu____27820 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27820
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27853 ->
                                                     let uu____27854 =
                                                       let uu____27860 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27860)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27854 r
                                                  in
                                               let uu____27866 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____27901  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____27901
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____27922 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____27922
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27866
                                                in
                                             match uu____27751 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____27947 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____27947
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____27948 =
                                                   let g_sort_is =
                                                     let uu____27958 =
                                                       let uu____27959 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____27959.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____27958 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____27964,uu____27965::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28025 ->
                                                         let uu____28026 =
                                                           let uu____28032 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28032)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28026 r
                                                      in
                                                   let uu____28038 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28073  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28073
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28094
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28094
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28038
                                                    in
                                                 (match uu____27948 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28121 =
                                                          let uu____28126 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28127 =
                                                            let uu____28128 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28128
                                                             in
                                                          (uu____28126,
                                                            uu____28127)
                                                           in
                                                        match uu____28121
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28156 =
                                                          let uu____28159 =
                                                            let uu____28162 =
                                                              let uu____28165
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28165
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28162
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28159
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28156
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28189 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28189
                                                           in
                                                        match g_lift.FStar_TypeChecker_Common.guard_f
                                                        with
                                                        | FStar_TypeChecker_Common.Trivial
                                                             -> guard
                                                        | FStar_TypeChecker_Common.NonTrivial
                                                            f ->
                                                            FStar_Syntax_Util.mk_conj
                                                              guard f
                                                         in
                                                      let wl7 =
                                                        let uu____28200 =
                                                          let uu____28203 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28206  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28206)
                                                            uu____28203
                                                           in
                                                        solve_prob orig
                                                          uu____28200 [] wl6
                                                         in
                                                      let uu____28207 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28207))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28230 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28232 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28232]
              | x -> x  in
            let c12 =
              let uu___3663_28235 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3663_28235.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3663_28235.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3663_28235.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3663_28235.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28236 =
              let uu____28241 =
                FStar_All.pipe_right
                  (let uu___3666_28243 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3666_28243.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3666_28243.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3666_28243.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3666_28243.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28241
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28236
              (fun uu____28257  ->
                 match uu____28257 with
                 | (c,g) ->
                     let uu____28264 =
                       let uu____28266 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28266  in
                     if uu____28264
                     then
                       let uu____28269 =
                         let uu____28275 =
                           let uu____28277 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28279 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28277 uu____28279
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28275)
                          in
                       FStar_Errors.raise_error uu____28269 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28285 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28285
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28291 = lift_c1 ()  in
               solve_eq uu____28291 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28300  ->
                         match uu___31_28300 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28305 -> false))
                  in
               let uu____28307 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28337)::uu____28338,(wp2,uu____28340)::uu____28341)
                     -> (wp1, wp2)
                 | uu____28414 ->
                     let uu____28439 =
                       let uu____28445 =
                         let uu____28447 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28449 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28447 uu____28449
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28445)
                        in
                     FStar_Errors.raise_error uu____28439
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28307 with
               | (wpc1,wpc2) ->
                   let uu____28459 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28459
                   then
                     let uu____28462 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28462 wl
                   else
                     (let uu____28466 =
                        let uu____28473 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28473  in
                      match uu____28466 with
                      | (c2_decl,qualifiers) ->
                          let uu____28494 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28494
                          then
                            let c1_repr =
                              let uu____28501 =
                                let uu____28502 =
                                  let uu____28503 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28503  in
                                let uu____28504 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28502 uu____28504
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28501
                               in
                            let c2_repr =
                              let uu____28507 =
                                let uu____28508 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28509 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28508 uu____28509
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28507
                               in
                            let uu____28511 =
                              let uu____28516 =
                                let uu____28518 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28520 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28518
                                  uu____28520
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28516
                               in
                            (match uu____28511 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28526 = attempt [prob] wl2  in
                                 solve env uu____28526)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28546 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28546
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28569 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28569
                                      then
                                        FStar_Util.print_string
                                          "Using trivial wp ... \n"
                                      else ());
                                     (let c1_univ =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env
                                          c11.FStar_Syntax_Syntax.result_typ
                                         in
                                      let trivial =
                                        let uu____28579 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28579 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28586 =
                                        let uu____28593 =
                                          let uu____28594 =
                                            let uu____28611 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28614 =
                                              let uu____28625 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28625; wpc1_2]  in
                                            (uu____28611, uu____28614)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28594
                                           in
                                        FStar_Syntax_Syntax.mk uu____28593
                                         in
                                      uu____28586
                                        FStar_Pervasives_Native.None r))
                                  else
                                    (let c2_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c21.FStar_Syntax_Syntax.result_typ
                                        in
                                     let stronger =
                                       FStar_All.pipe_right c2_decl
                                         FStar_Syntax_Util.get_stronger_vc_combinator
                                        in
                                     let uu____28674 =
                                       let uu____28681 =
                                         let uu____28682 =
                                           let uu____28699 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28702 =
                                             let uu____28713 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28722 =
                                               let uu____28733 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28733; wpc1_2]  in
                                             uu____28713 :: uu____28722  in
                                           (uu____28699, uu____28702)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28682
                                          in
                                       FStar_Syntax_Syntax.mk uu____28681  in
                                     uu____28674 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28787 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28787
                              then
                                let uu____28792 =
                                  let uu____28794 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28794
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28792
                              else ());
                             (let uu____28798 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28798 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28807 =
                                      let uu____28810 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28813  ->
                                           FStar_Pervasives_Native.Some
                                             _28813) uu____28810
                                       in
                                    solve_prob orig uu____28807 [] wl1  in
                                  let uu____28814 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28814))))
           in
        let uu____28815 = FStar_Util.physical_equality c1 c2  in
        if uu____28815
        then
          let uu____28818 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28818
        else
          ((let uu____28822 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28822
            then
              let uu____28827 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28829 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28827
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28829
            else ());
           (let uu____28834 =
              let uu____28843 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28846 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28843, uu____28846)  in
            match uu____28834 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28864),FStar_Syntax_Syntax.Total
                    (t2,uu____28866)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28883 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28883 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28885,FStar_Syntax_Syntax.Total uu____28886) ->
                     let uu____28903 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____28903 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28907),FStar_Syntax_Syntax.Total
                    (t2,uu____28909)) ->
                     let uu____28926 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28926 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28929),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28931)) ->
                     let uu____28948 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28948 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28951),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28953)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____28970 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28970 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28973),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28975)) ->
                     let uu____28992 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____28992 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28995,FStar_Syntax_Syntax.Comp uu____28996) ->
                     let uu____29005 =
                       let uu___3790_29008 = problem  in
                       let uu____29011 =
                         let uu____29012 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29012
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29008.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29011;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29008.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29008.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29008.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29008.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29008.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29008.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29008.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29008.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29005 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29013,FStar_Syntax_Syntax.Comp uu____29014) ->
                     let uu____29023 =
                       let uu___3790_29026 = problem  in
                       let uu____29029 =
                         let uu____29030 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29030
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3790_29026.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29029;
                         FStar_TypeChecker_Common.relation =
                           (uu___3790_29026.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3790_29026.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3790_29026.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3790_29026.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3790_29026.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3790_29026.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3790_29026.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3790_29026.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29023 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29031,FStar_Syntax_Syntax.GTotal uu____29032) ->
                     let uu____29041 =
                       let uu___3802_29044 = problem  in
                       let uu____29047 =
                         let uu____29048 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29048
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29044.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29044.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29044.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29047;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29044.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29044.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29044.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29044.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29044.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29044.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29041 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29049,FStar_Syntax_Syntax.Total uu____29050) ->
                     let uu____29059 =
                       let uu___3802_29062 = problem  in
                       let uu____29065 =
                         let uu____29066 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29066
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3802_29062.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3802_29062.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3802_29062.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29065;
                         FStar_TypeChecker_Common.element =
                           (uu___3802_29062.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3802_29062.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3802_29062.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3802_29062.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3802_29062.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3802_29062.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29059 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29067,FStar_Syntax_Syntax.Comp uu____29068) ->
                     let uu____29069 =
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
                     if uu____29069
                     then
                       let uu____29072 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29072 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29079 =
                            let uu____29084 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29084
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29093 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29094 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29093, uu____29094))
                             in
                          match uu____29079 with
                          | (c1_comp1,c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____29102 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29102
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29110 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29110 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29113 =
                                  FStar_Thunk.mk
                                    (fun uu____29118  ->
                                       let uu____29119 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29121 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29119 uu____29121)
                                   in
                                giveup env uu____29113 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29132 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29132 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29182 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29182 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29207 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29238  ->
                match uu____29238 with
                | (u1,u2) ->
                    let uu____29246 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29248 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29246 uu____29248))
         in
      FStar_All.pipe_right uu____29207 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29285,[])) when
          let uu____29312 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29312 -> "{}"
      | uu____29315 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29342 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29342
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29354 =
              FStar_List.map
                (fun uu____29367  ->
                   match uu____29367 with
                   | (uu____29374,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29354 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29385 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29385 imps
  
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
                  let uu____29442 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29442
                  then
                    let uu____29450 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29452 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29450
                      (rel_to_string rel) uu____29452
                  else "TOP"  in
                let uu____29458 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29458 with
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
              let uu____29518 =
                let uu____29521 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29524  -> FStar_Pervasives_Native.Some _29524)
                  uu____29521
                 in
              FStar_Syntax_Syntax.new_bv uu____29518 t1  in
            let uu____29525 =
              let uu____29530 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29530
               in
            match uu____29525 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____29588 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29588
         then
           let uu____29593 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29593
         else ());
        (let uu____29600 =
           FStar_Util.record_time (fun uu____29607  -> solve env probs)  in
         match uu____29600 with
         | (sol,ms) ->
             ((let uu____29619 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29619
               then
                 let uu____29624 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29624
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29637 =
                     FStar_Util.record_time
                       (fun uu____29644  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29637 with
                    | ((),ms1) ->
                        ((let uu____29655 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29655
                          then
                            let uu____29660 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29660
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29672 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29672
                     then
                       let uu____29679 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29679
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____29705 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29705
            then
              let uu____29710 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29710
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29718 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29718
             then
               let uu____29723 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29723
             else ());
            (let f2 =
               let uu____29729 =
                 let uu____29730 = FStar_Syntax_Util.unmeta f1  in
                 uu____29730.FStar_Syntax_Syntax.n  in
               match uu____29729 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29734 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3919_29735 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3919_29735.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3919_29735.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3919_29735.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred *
        FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____29778 =
              let uu____29779 =
                let uu____29780 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29781  ->
                       FStar_TypeChecker_Common.NonTrivial _29781)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29780;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29779  in
            FStar_All.pipe_left
              (fun _29788  -> FStar_Pervasives_Native.Some _29788)
              uu____29778
  
let with_guard_no_simp :
  'Auu____29798 .
    'Auu____29798 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____29838 =
              let uu____29839 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29840  -> FStar_TypeChecker_Common.NonTrivial _29840)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29839;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29838
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____29873 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29873
           then
             let uu____29878 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29880 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29878
               uu____29880
           else ());
          (let uu____29885 =
             let uu____29890 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29890
              in
           match uu____29885 with
           | (prob,wl) ->
               let g =
                 let uu____29898 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29906  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29898  in
               ((let uu____29924 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29924
                 then
                   let uu____29929 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29929
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29950 = try_teq true env t1 t2  in
        match uu____29950 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____29955 = FStar_TypeChecker_Env.get_range env  in
              let uu____29956 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____29955 uu____29956);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____29964 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____29964
              then
                let uu____29969 = FStar_Syntax_Print.term_to_string t1  in
                let uu____29971 = FStar_Syntax_Print.term_to_string t2  in
                let uu____29973 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____29969
                  uu____29971 uu____29973
              else ());
             g)
  
let (get_teq_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____29997 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____29997
         then
           let uu____30002 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30004 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30002
             uu____30004
         else ());
        (let uu____30009 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30009 with
         | (prob,x,wl) ->
             let g =
               let uu____30024 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30033  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30024  in
             ((let uu____30051 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30051
               then
                 let uu____30056 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30056
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30064 =
                     let uu____30065 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30065 g1  in
                   FStar_Pervasives_Native.Some uu____30064)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30087 = FStar_TypeChecker_Env.get_range env  in
          let uu____30088 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30087 uu____30088
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____30117 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30117
         then
           let uu____30122 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30124 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30122 uu____30124
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30135 =
           let uu____30142 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30142 "sub_comp"
            in
         match uu____30135 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30155 =
                 FStar_Util.record_time
                   (fun uu____30167  ->
                      let uu____30168 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30177  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30168)
                  in
               match uu____30155 with
               | (r,ms) ->
                   ((let uu____30205 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30205
                     then
                       let uu____30210 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30212 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30214 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30210 uu____30212
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30214
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
      fun uu____30252  ->
        match uu____30252 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30295 =
                 let uu____30301 =
                   let uu____30303 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30305 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30303 uu____30305
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30301)  in
               let uu____30309 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30295 uu____30309)
               in
            let equiv1 v1 v' =
              let uu____30322 =
                let uu____30327 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30328 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30327, uu____30328)  in
              match uu____30322 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30348 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30379 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30379 with
                      | FStar_Syntax_Syntax.U_unif uu____30386 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30415  ->
                                    match uu____30415 with
                                    | (u,v') ->
                                        let uu____30424 = equiv1 v1 v'  in
                                        if uu____30424
                                        then
                                          let uu____30429 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30429 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30450 -> []))
               in
            let uu____30455 =
              let wl =
                let uu___4030_30459 = empty_worklist env  in
                {
                  attempting = (uu___4030_30459.attempting);
                  wl_deferred = (uu___4030_30459.wl_deferred);
                  ctr = (uu___4030_30459.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4030_30459.smt_ok);
                  umax_heuristic_ok = (uu___4030_30459.umax_heuristic_ok);
                  tcenv = (uu___4030_30459.tcenv);
                  wl_implicits = (uu___4030_30459.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30478  ->
                      match uu____30478 with
                      | (lb,v1) ->
                          let uu____30485 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30485 with
                           | USolved wl1 -> ()
                           | uu____30488 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30499 =
              match uu____30499 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30511) -> true
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
                      uu____30535,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30537,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30548) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30556,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30565 -> false)
               in
            let uu____30571 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30588  ->
                      match uu____30588 with
                      | (u,v1) ->
                          let uu____30596 = check_ineq (u, v1)  in
                          if uu____30596
                          then true
                          else
                            ((let uu____30604 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30604
                              then
                                let uu____30609 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30611 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30609
                                  uu____30611
                              else ());
                             false)))
               in
            if uu____30571
            then ()
            else
              ((let uu____30621 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30621
                then
                  ((let uu____30627 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30627);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30639 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30639))
                else ());
               (let uu____30652 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30652))
  
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
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____30725 =
          match uu____30725 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4107_30748 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4107_30748.attempting);
            wl_deferred = (uu___4107_30748.wl_deferred);
            ctr = (uu___4107_30748.ctr);
            defer_ok;
            smt_ok = (uu___4107_30748.smt_ok);
            umax_heuristic_ok = (uu___4107_30748.umax_heuristic_ok);
            tcenv = (uu___4107_30748.tcenv);
            wl_implicits = (uu___4107_30748.wl_implicits)
          }  in
        (let uu____30751 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30751
         then
           let uu____30756 = FStar_Util.string_of_bool defer_ok  in
           let uu____30758 = wl_to_string wl  in
           let uu____30760 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30756 uu____30758 uu____30760
         else ());
        (let g1 =
           let uu____30766 = solve_and_commit env wl fail1  in
           match uu____30766 with
           | FStar_Pervasives_Native.Some
               (uu____30773::uu____30774,uu____30775) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4122_30804 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4122_30804.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4122_30804.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30805 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4127_30814 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4127_30814.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4127_30814.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4127_30814.FStar_TypeChecker_Common.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
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
            let uu___4139_30891 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4139_30891.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4139_30891.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4139_30891.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30892 =
            let uu____30894 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30894  in
          if uu____30892
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30906 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30907 =
                       let uu____30909 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30909
                        in
                     FStar_Errors.diag uu____30906 uu____30907)
                  else ();
                  (let vc1 =
                     let uu____30915 =
                       let uu____30919 =
                         let uu____30921 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____30921  in
                       FStar_Pervasives_Native.Some uu____30919  in
                     FStar_Profiling.profile
                       (fun uu____30924  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____30915 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____30928 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30929 =
                        let uu____30931 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30931
                         in
                      FStar_Errors.diag uu____30928 uu____30929)
                   else ();
                   (let uu____30937 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____30937
                      "discharge_guard'" env vc1);
                   (let uu____30939 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____30939 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____30948 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30949 =
                                let uu____30951 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____30951
                                 in
                              FStar_Errors.diag uu____30948 uu____30949)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____30961 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30962 =
                                let uu____30964 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____30964
                                 in
                              FStar_Errors.diag uu____30961 uu____30962)
                           else ();
                           (let vcs =
                              let uu____30978 = FStar_Options.use_tactics ()
                                 in
                              if uu____30978
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31000  ->
                                     (let uu____31002 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31002);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31046  ->
                                              match uu____31046 with
                                              | (env1,goal,opts) ->
                                                  let uu____31062 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31062, opts)))))
                              else
                                (let uu____31066 =
                                   let uu____31073 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31073)  in
                                 [uu____31066])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31106  ->
                                    match uu____31106 with
                                    | (env1,goal,opts) ->
                                        let uu____31116 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31116 with
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
                                              if debug1
                                              then
                                                (let uu____31127 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31128 =
                                                   let uu____31130 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31132 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31130 uu____31132
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31127 uu____31128)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31139 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31140 =
                                                   let uu____31142 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31142
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31139 uu____31140)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31160 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31160 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31169 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31169
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31183 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31183 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31213 = try_teq false env t1 t2  in
        match uu____31213 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____31257 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31257 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31270 ->
                     let uu____31283 =
                       let uu____31284 = FStar_Syntax_Subst.compress r  in
                       uu____31284.FStar_Syntax_Syntax.n  in
                     (match uu____31283 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31289) ->
                          unresolved ctx_u'
                      | uu____31306 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31330 = acc  in
            match uu____31330 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31349 = hd1  in
                     (match uu____31349 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31360 = unresolved ctx_u  in
                             if uu____31360
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31384 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31384
                                     then
                                       let uu____31388 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31388
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31397 = teq_nosmt env1 t tm
                                          in
                                       match uu____31397 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4252_31407 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4252_31407.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4252_31407.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4252_31407.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4252_31407.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4252_31407.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4252_31407.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4252_31407.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4255_31415 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4255_31415.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4255_31415.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4255_31415.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4259_31426 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4259_31426.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4259_31426.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4259_31426.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4259_31426.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4259_31426.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4259_31426.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4259_31426.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4259_31426.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4259_31426.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4259_31426.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4259_31426.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4259_31426.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4259_31426.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4259_31426.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4259_31426.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4259_31426.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4259_31426.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4259_31426.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4259_31426.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4259_31426.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4259_31426.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4259_31426.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4259_31426.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4259_31426.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4259_31426.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4259_31426.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4259_31426.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4259_31426.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4259_31426.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4259_31426.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4259_31426.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4259_31426.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4259_31426.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4259_31426.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4259_31426.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4259_31426.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4259_31426.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4259_31426.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4259_31426.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4259_31426.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4259_31426.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4259_31426.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4259_31426.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4259_31426.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4259_31426.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4259_31426.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4264_31431 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4264_31431.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4264_31431.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4264_31431.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4264_31431.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4264_31431.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4264_31431.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4264_31431.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4264_31431.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4264_31431.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4264_31431.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4264_31431.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4264_31431.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4264_31431.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4264_31431.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4264_31431.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4264_31431.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4264_31431.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4264_31431.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4264_31431.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4264_31431.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4264_31431.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4264_31431.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4264_31431.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4264_31431.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4264_31431.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4264_31431.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4264_31431.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4264_31431.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4264_31431.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4264_31431.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4264_31431.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4264_31431.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4264_31431.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4264_31431.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4264_31431.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4264_31431.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4264_31431.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31436 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31436
                                   then
                                     let uu____31441 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31443 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31445 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31447 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31441 uu____31443 uu____31445
                                       reason uu____31447
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4270_31454  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31461 =
                                             let uu____31471 =
                                               let uu____31479 =
                                                 let uu____31481 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31483 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31485 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31481 uu____31483
                                                   uu____31485
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31479, r)
                                                in
                                             [uu____31471]  in
                                           FStar_Errors.add_errors
                                             uu____31461);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31504 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31515  ->
                                               let uu____31516 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31518 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31520 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31516 uu____31518
                                                 reason uu____31520)) env2 g1
                                         true
                                        in
                                     match uu____31504 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl1)))))
             in
          let uu___4282_31528 = g  in
          let uu____31529 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4282_31528.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4282_31528.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4282_31528.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31529
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____31569 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31569 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31570 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31570
      | imp::uu____31572 ->
          let uu____31575 =
            let uu____31581 =
              let uu____31583 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31585 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31583 uu____31585
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31581)
             in
          FStar_Errors.raise_error uu____31575
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31605 = teq env t1 t2  in
        force_trivial_guard env uu____31605
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31624 = teq_nosmt env t1 t2  in
        match uu____31624 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4307_31643 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4307_31643.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4307_31643.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4307_31643.FStar_TypeChecker_Common.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31679 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31679
         then
           let uu____31684 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31686 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31684
             uu____31686
         else ());
        (let uu____31691 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31691 with
         | (prob,x,wl) ->
             let g =
               let uu____31710 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31719  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31710  in
             ((let uu____31737 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31737
               then
                 let uu____31742 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31744 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31746 =
                   let uu____31748 = FStar_Util.must g  in
                   guard_to_string env uu____31748  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31742 uu____31744 uu____31746
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
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31785 = check_subtyping env t1 t2  in
        match uu____31785 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31804 =
              let uu____31805 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31805 g  in
            FStar_Pervasives_Native.Some uu____31804
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31824 = check_subtyping env t1 t2  in
        match uu____31824 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31843 =
              let uu____31844 =
                let uu____31845 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31845]  in
              FStar_TypeChecker_Env.close_guard env uu____31844 g  in
            FStar_Pervasives_Native.Some uu____31843
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31883 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31883
         then
           let uu____31888 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31890 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31888
             uu____31890
         else ());
        (let uu____31895 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31895 with
         | (prob,x,wl) ->
             let g =
               let uu____31910 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31919  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31910  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____31940 =
                      let uu____31941 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31941]  in
                    FStar_TypeChecker_Env.close_guard env uu____31940 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31982 = subtype_nosmt env t1 t2  in
        match uu____31982 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  