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
    match projectee with | TERM _0 -> true | uu____50 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____85 -> false
  
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
                FStar_Syntax_Syntax.ctx_uvar_meta_t
                  FStar_Pervasives_Native.option ->
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
                    let uu____530 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____530;
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
                   (let uu____562 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____562
                    then
                      let uu____566 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____566
                    else ());
                   (ctx_uvar, t,
                     ((let uu___73_572 = wl  in
                       {
                         attempting = (uu___73_572.attempting);
                         wl_deferred = (uu___73_572.wl_deferred);
                         ctr = (uu___73_572.ctr);
                         defer_ok = (uu___73_572.defer_ok);
                         smt_ok = (uu___73_572.smt_ok);
                         umax_heuristic_ok = (uu___73_572.umax_heuristic_ok);
                         tcenv = (uu___73_572.tcenv);
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
            let uu___79_605 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___79_605.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___79_605.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___79_605.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___79_605.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___79_605.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___79_605.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___79_605.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___79_605.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___79_605.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___79_605.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___79_605.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___79_605.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___79_605.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___79_605.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___79_605.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___79_605.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___79_605.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___79_605.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___79_605.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___79_605.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___79_605.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___79_605.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___79_605.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___79_605.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___79_605.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___79_605.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___79_605.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___79_605.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___79_605.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___79_605.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___79_605.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___79_605.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___79_605.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___79_605.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___79_605.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___79_605.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___79_605.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___79_605.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___79_605.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___79_605.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___79_605.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___79_605.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___79_605.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___79_605.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___79_605.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___79_605.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____607 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____607 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____694 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____729 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____759 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____770 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____781 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_799  ->
    match uu___0_799 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____811 = FStar_Syntax_Util.head_and_args t  in
    match uu____811 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____874 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____876 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____891 =
                     let uu____893 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____893  in
                   FStar_Util.format1 "@<%s>" uu____891
                in
             let uu____897 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____874 uu____876 uu____897
         | uu____900 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_912  ->
      match uu___1_912 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____917 =
            let uu____921 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____923 =
              let uu____927 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____929 =
                let uu____933 =
                  let uu____937 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____937]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____933
                 in
              uu____927 :: uu____929  in
            uu____921 :: uu____923  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____917
      | FStar_TypeChecker_Common.CProb p ->
          let uu____948 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____950 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____952 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____948 uu____950
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____952
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_966  ->
      match uu___2_966 with
      | UNIV (u,t) ->
          let x =
            let uu____972 = FStar_Options.hide_uvar_nums ()  in
            if uu____972
            then "?"
            else
              (let uu____979 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____979 FStar_Util.string_of_int)
             in
          let uu____983 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____983
      | TERM (u,t) ->
          let x =
            let uu____990 = FStar_Options.hide_uvar_nums ()  in
            if uu____990
            then "?"
            else
              (let uu____997 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____997 FStar_Util.string_of_int)
             in
          let uu____1001 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1001
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1020 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1020 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1041 =
      let uu____1045 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1045
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1041 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1064 .
    (FStar_Syntax_Syntax.term * 'Auu____1064) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1083 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1104  ->
              match uu____1104 with
              | (x,uu____1111) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1083 (FStar_String.concat " ")
  
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
        (let uu____1151 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1151
         then
           let uu____1156 = FStar_Thunk.force reason  in
           let uu____1159 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1156 uu____1159
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1182 = FStar_Thunk.mk (fun uu____1185  -> reason)  in
        giveup env uu____1182 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1191  ->
    match uu___3_1191 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1197 .
    'Auu____1197 FStar_TypeChecker_Common.problem ->
      'Auu____1197 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___143_1209 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___143_1209.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___143_1209.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___143_1209.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___143_1209.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___143_1209.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___143_1209.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___143_1209.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1217 .
    'Auu____1217 FStar_TypeChecker_Common.problem ->
      'Auu____1217 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1237  ->
    match uu___4_1237 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1243  -> FStar_TypeChecker_Common.TProb _1243)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1249  -> FStar_TypeChecker_Common.CProb _1249)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1255  ->
    match uu___5_1255 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___155_1261 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___155_1261.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___155_1261.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___155_1261.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___155_1261.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___155_1261.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___155_1261.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___155_1261.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___155_1261.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___155_1261.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___159_1269 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___159_1269.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___159_1269.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___159_1269.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___159_1269.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___159_1269.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___159_1269.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___159_1269.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___159_1269.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___159_1269.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1282  ->
      match uu___6_1282 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1289  ->
    match uu___7_1289 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1302  ->
    match uu___8_1302 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1317  ->
    match uu___9_1317 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1332  ->
    match uu___10_1332 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1346  ->
    match uu___11_1346 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1360  ->
    match uu___12_1360 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1372  ->
    match uu___13_1372 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1388 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1388) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1418 =
          let uu____1420 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1420  in
        if uu____1418
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1457)::bs ->
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
          let uu____1504 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1528 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1528]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1504
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1556 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1580 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1580]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1556
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1627 =
          let uu____1629 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1629  in
        if uu____1627
        then ()
        else
          (let uu____1634 =
             let uu____1637 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1637
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1634 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1686 =
          let uu____1688 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1688  in
        if uu____1686
        then ()
        else
          (let uu____1693 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1693)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1713 =
        let uu____1715 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1715  in
      if uu____1713
      then ()
      else
        (let msgf m =
           let uu____1729 =
             let uu____1731 =
               let uu____1733 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1733 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1731  in
           Prims.op_Hat msg uu____1729  in
         (let uu____1738 = msgf "scope"  in
          let uu____1741 = p_scope prob  in
          def_scope_wf uu____1738 (p_loc prob) uu____1741);
         (let uu____1753 = msgf "guard"  in
          def_check_scoped uu____1753 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1760 = msgf "lhs"  in
                def_check_scoped uu____1760 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1763 = msgf "rhs"  in
                def_check_scoped uu____1763 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1770 = msgf "lhs"  in
                def_check_scoped_comp uu____1770 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1773 = msgf "rhs"  in
                def_check_scoped_comp uu____1773 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___252_1794 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___252_1794.wl_deferred);
          ctr = (uu___252_1794.ctr);
          defer_ok = (uu___252_1794.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___252_1794.umax_heuristic_ok);
          tcenv = (uu___252_1794.tcenv);
          wl_implicits = (uu___252_1794.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1802 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1802 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___256_1825 = empty_worklist env  in
      let uu____1826 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1826;
        wl_deferred = (uu___256_1825.wl_deferred);
        ctr = (uu___256_1825.ctr);
        defer_ok = (uu___256_1825.defer_ok);
        smt_ok = (uu___256_1825.smt_ok);
        umax_heuristic_ok = (uu___256_1825.umax_heuristic_ok);
        tcenv = (uu___256_1825.tcenv);
        wl_implicits = (uu___256_1825.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___261_1847 = wl  in
        {
          attempting = (uu___261_1847.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___261_1847.ctr);
          defer_ok = (uu___261_1847.defer_ok);
          smt_ok = (uu___261_1847.smt_ok);
          umax_heuristic_ok = (uu___261_1847.umax_heuristic_ok);
          tcenv = (uu___261_1847.tcenv);
          wl_implicits = (uu___261_1847.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1874 = FStar_Thunk.mkv reason  in defer uu____1874 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___269_1893 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___269_1893.wl_deferred);
         ctr = (uu___269_1893.ctr);
         defer_ok = (uu___269_1893.defer_ok);
         smt_ok = (uu___269_1893.smt_ok);
         umax_heuristic_ok = (uu___269_1893.umax_heuristic_ok);
         tcenv = (uu___269_1893.tcenv);
         wl_implicits = (uu___269_1893.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1907 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1907 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1941 = FStar_Syntax_Util.type_u ()  in
            match uu____1941 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1953 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1953 with
                 | (uu____1965,tt,wl1) ->
                     let uu____1968 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1968, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1974  ->
    match uu___14_1974 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _1980  -> FStar_TypeChecker_Common.TProb _1980) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _1986  -> FStar_TypeChecker_Common.CProb _1986) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1994 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1994 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2014  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2056 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2056 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2056 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2056 FStar_TypeChecker_Common.problem *
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
                        let uu____2143 =
                          let uu____2152 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2152]  in
                        FStar_List.append scope uu____2143
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2195 =
                      let uu____2198 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2198  in
                    FStar_List.append uu____2195
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2217 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2217 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2237 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2237;
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
                  (let uu____2311 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2311 with
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
                  (let uu____2399 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2399 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2437 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2437 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2437 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2437 FStar_TypeChecker_Common.problem *
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
                          let uu____2505 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2505]  in
                        let uu____2524 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2524
                     in
                  let uu____2527 =
                    let uu____2534 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___352_2545 = wl  in
                       {
                         attempting = (uu___352_2545.attempting);
                         wl_deferred = (uu___352_2545.wl_deferred);
                         ctr = (uu___352_2545.ctr);
                         defer_ok = (uu___352_2545.defer_ok);
                         smt_ok = (uu___352_2545.smt_ok);
                         umax_heuristic_ok =
                           (uu___352_2545.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___352_2545.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2534
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2527 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2557 =
                              let uu____2562 =
                                let uu____2563 =
                                  let uu____2572 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2572
                                   in
                                [uu____2563]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2562  in
                            uu____2557 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2600 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2600;
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
                let uu____2648 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2648;
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
  'Auu____2663 .
    worklist ->
      'Auu____2663 FStar_TypeChecker_Common.problem ->
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
              let uu____2696 =
                let uu____2699 =
                  let uu____2700 =
                    let uu____2707 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2707)  in
                  FStar_Syntax_Syntax.NT uu____2700  in
                [uu____2699]  in
              FStar_Syntax_Subst.subst uu____2696 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2729 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2729
        then
          let uu____2737 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2740 = prob_to_string env d  in
          let uu____2742 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2749 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2737 uu____2740 uu____2742 uu____2749
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2761 -> failwith "impossible"  in
           let uu____2764 =
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
           match uu____2764 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2807  ->
            match uu___15_2807 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2819 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2823 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2823 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2854  ->
           match uu___16_2854 with
           | UNIV uu____2857 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2864 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2864
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
        (fun uu___17_2892  ->
           match uu___17_2892 with
           | UNIV (u',t) ->
               let uu____2897 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2897
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2904 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2916 =
        let uu____2917 =
          let uu____2918 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2918
           in
        FStar_Syntax_Subst.compress uu____2917  in
      FStar_All.pipe_right uu____2916 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2930 =
        let uu____2931 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2931  in
      FStar_All.pipe_right uu____2930 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2943 =
        let uu____2947 =
          let uu____2949 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2949  in
        FStar_Pervasives_Native.Some uu____2947  in
      FStar_Profiling.profile (fun uu____2952  -> sn' env t) uu____2943
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
          let uu____2977 =
            let uu____2981 =
              let uu____2983 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____2983  in
            FStar_Pervasives_Native.Some uu____2981  in
          FStar_Profiling.profile
            (fun uu____2986  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____2977
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2994 = FStar_Syntax_Util.head_and_args t  in
    match uu____2994 with
    | (h,uu____3013) ->
        let uu____3038 =
          let uu____3039 = FStar_Syntax_Subst.compress h  in
          uu____3039.FStar_Syntax_Syntax.n  in
        (match uu____3038 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3044 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3057 =
        let uu____3061 =
          let uu____3063 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3063  in
        FStar_Pervasives_Native.Some uu____3061  in
      FStar_Profiling.profile
        (fun uu____3068  ->
           let uu____3069 = should_strongly_reduce t  in
           if uu____3069
           then
             let uu____3072 =
               let uu____3073 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3073  in
             FStar_All.pipe_right uu____3072 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3057 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3084 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3084) ->
        (FStar_Syntax_Syntax.term * 'Auu____3084)
  =
  fun env  ->
    fun t  ->
      let uu____3107 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3107, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3159  ->
              match uu____3159 with
              | (x,imp) ->
                  let uu____3178 =
                    let uu___458_3179 = x  in
                    let uu____3180 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___458_3179.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___458_3179.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3180
                    }  in
                  (uu____3178, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3204 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3204
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3208 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3208
        | uu____3211 -> u2  in
      let uu____3212 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3212
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3229 =
          let uu____3233 =
            let uu____3235 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3235  in
          FStar_Pervasives_Native.Some uu____3233  in
        FStar_Profiling.profile
          (fun uu____3238  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3229 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3360 = norm_refinement env t12  in
                 match uu____3360 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3375;
                     FStar_Syntax_Syntax.vars = uu____3376;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3400 =
                       let uu____3402 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3404 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3402 uu____3404
                        in
                     failwith uu____3400)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3420 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3420
          | FStar_Syntax_Syntax.Tm_uinst uu____3421 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3458 =
                   let uu____3459 = FStar_Syntax_Subst.compress t1'  in
                   uu____3459.FStar_Syntax_Syntax.n  in
                 match uu____3458 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3474 -> aux true t1'
                 | uu____3482 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3497 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3528 =
                   let uu____3529 = FStar_Syntax_Subst.compress t1'  in
                   uu____3529.FStar_Syntax_Syntax.n  in
                 match uu____3528 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3544 -> aux true t1'
                 | uu____3552 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3567 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3614 =
                   let uu____3615 = FStar_Syntax_Subst.compress t1'  in
                   uu____3615.FStar_Syntax_Syntax.n  in
                 match uu____3614 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3630 -> aux true t1'
                 | uu____3638 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3653 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3668 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3683 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3698 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3713 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3742 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3775 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3796 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3823 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3851 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3888 ->
              let uu____3895 =
                let uu____3897 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3899 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3897 uu____3899
                 in
              failwith uu____3895
          | FStar_Syntax_Syntax.Tm_ascribed uu____3914 ->
              let uu____3941 =
                let uu____3943 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3945 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3943 uu____3945
                 in
              failwith uu____3941
          | FStar_Syntax_Syntax.Tm_delayed uu____3960 ->
              let uu____3975 =
                let uu____3977 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3979 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3977 uu____3979
                 in
              failwith uu____3975
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3994 =
                let uu____3996 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3998 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3996 uu____3998
                 in
              failwith uu____3994
           in
        let uu____4013 = whnf env t1  in aux false uu____4013
  
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
      let uu____4058 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4058 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4099 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4099, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4126 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4126 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4186  ->
    match uu____4186 with
    | (t_base,refopt) ->
        let uu____4217 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4217 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4259 =
      let uu____4263 =
        let uu____4266 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4291  ->
                  match uu____4291 with | (uu____4299,uu____4300,x) -> x))
           in
        FStar_List.append wl.attempting uu____4266  in
      FStar_List.map (wl_prob_to_string wl) uu____4263  in
    FStar_All.pipe_right uu____4259 (FStar_String.concat "\n\t")
  
type flex_t =
  | Flex of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
  FStar_Syntax_Syntax.args) 
let (uu___is_Flex : flex_t -> Prims.bool) = fun projectee  -> true 
let (__proj__Flex__item___0 :
  flex_t ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
      FStar_Syntax_Syntax.args))
  = fun projectee  -> match projectee with | Flex _0 -> _0 
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4360  ->
    match uu____4360 with
    | Flex (uu____4362,c,args) ->
        let uu____4365 = print_ctx_uvar c  in
        let uu____4367 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4365 uu____4367
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4377 = FStar_Syntax_Util.head_and_args t  in
    match uu____4377 with
    | (head1,_args) ->
        let uu____4421 =
          let uu____4422 = FStar_Syntax_Subst.compress head1  in
          uu____4422.FStar_Syntax_Syntax.n  in
        (match uu____4421 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4426 -> true
         | uu____4440 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4448 = FStar_Syntax_Util.head_and_args t  in
    match uu____4448 with
    | (head1,_args) ->
        let uu____4491 =
          let uu____4492 = FStar_Syntax_Subst.compress head1  in
          uu____4492.FStar_Syntax_Syntax.n  in
        (match uu____4491 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4496) -> u
         | uu____4513 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4538 = FStar_Syntax_Util.head_and_args t  in
      match uu____4538 with
      | (head1,args) ->
          let uu____4585 =
            let uu____4586 = FStar_Syntax_Subst.compress head1  in
            uu____4586.FStar_Syntax_Syntax.n  in
          (match uu____4585 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4594)) ->
               ((Flex (t, uv, args)), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4627 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4652  ->
                         match uu___18_4652 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4657 =
                               let uu____4658 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4658.FStar_Syntax_Syntax.n  in
                             (match uu____4657 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4663 -> false)
                         | uu____4665 -> true))
                  in
               (match uu____4627 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4690 =
                        FStar_List.collect
                          (fun uu___19_4702  ->
                             match uu___19_4702 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4706 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4706]
                             | uu____4707 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4690 FStar_List.rev  in
                    let uu____4730 =
                      let uu____4737 =
                        let uu____4746 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4768  ->
                                  match uu___20_4768 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4772 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4772]
                                  | uu____4773 -> []))
                           in
                        FStar_All.pipe_right uu____4746 FStar_List.rev  in
                      let uu____4796 =
                        let uu____4799 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4799  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4737 uu____4796
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4730 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4835  ->
                                match uu____4835 with
                                | (x,i) ->
                                    let uu____4854 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4854, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4885  ->
                                match uu____4885 with
                                | (a,i) ->
                                    let uu____4904 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4904, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((Flex (t1, v1, all_args)), wl1))))
           | uu____4926 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4948 =
          let uu____4971 =
            let uu____4972 = FStar_Syntax_Subst.compress k  in
            uu____4972.FStar_Syntax_Syntax.n  in
          match uu____4971 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5054 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5054)
              else
                (let uu____5089 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5089 with
                 | (ys',t1,uu____5122) ->
                     let uu____5127 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5127))
          | uu____5166 ->
              let uu____5167 =
                let uu____5172 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5172)  in
              ((ys, t), uu____5167)
           in
        match uu____4948 with
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
                 let uu____5267 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5267 c  in
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
               (let uu____5345 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5345
                then
                  let uu____5350 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5352 = print_ctx_uvar uv  in
                  let uu____5354 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5350 uu____5352 uu____5354
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5363 =
                   let uu____5365 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5365  in
                 let uu____5368 =
                   let uu____5371 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5371
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5363 uu____5368 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5404 =
               let uu____5405 =
                 let uu____5407 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5409 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5407 uu____5409
                  in
               failwith uu____5405  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5475  ->
                       match uu____5475 with
                       | (a,i) ->
                           let uu____5496 =
                             let uu____5497 = FStar_Syntax_Subst.compress a
                                in
                             uu____5497.FStar_Syntax_Syntax.n  in
                           (match uu____5496 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5523 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5533 =
                 let uu____5535 = is_flex g  in Prims.op_Negation uu____5535
                  in
               if uu____5533
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5544 = destruct_flex_t g wl  in
                  match uu____5544 with
                  | (Flex (uu____5549,uv1,args),wl1) ->
                      ((let uu____5554 = args_as_binders args  in
                        assign_solution uu____5554 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___715_5556 = wl1  in
              {
                attempting = (uu___715_5556.attempting);
                wl_deferred = (uu___715_5556.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___715_5556.defer_ok);
                smt_ok = (uu___715_5556.smt_ok);
                umax_heuristic_ok = (uu___715_5556.umax_heuristic_ok);
                tcenv = (uu___715_5556.tcenv);
                wl_implicits = (uu___715_5556.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5581 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5581
         then
           let uu____5586 = FStar_Util.string_of_int pid  in
           let uu____5588 =
             let uu____5590 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5590 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5586 uu____5588
         else ());
        commit sol;
        (let uu___723_5604 = wl  in
         {
           attempting = (uu___723_5604.attempting);
           wl_deferred = (uu___723_5604.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___723_5604.defer_ok);
           smt_ok = (uu___723_5604.smt_ok);
           umax_heuristic_ok = (uu___723_5604.umax_heuristic_ok);
           tcenv = (uu___723_5604.tcenv);
           wl_implicits = (uu___723_5604.wl_implicits)
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
          (let uu____5640 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5640
           then
             let uu____5645 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5649 =
               let uu____5651 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5651 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5645 uu____5649
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
        let uu____5686 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5686 FStar_Util.set_elements  in
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
      let uu____5726 = occurs uk t  in
      match uu____5726 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5765 =
                 let uu____5767 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5769 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5767 uu____5769
                  in
               FStar_Pervasives_Native.Some uu____5765)
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
            let uu____5889 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5889 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5940 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5997  ->
             match uu____5997 with
             | (x,uu____6009) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6027 = FStar_List.last bs  in
      match uu____6027 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6051) ->
          let uu____6062 =
            FStar_Util.prefix_until
              (fun uu___21_6077  ->
                 match uu___21_6077 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6080 -> false) g
             in
          (match uu____6062 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6094,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6131 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6131 with
        | (pfx,uu____6141) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6153 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6153 with
             | (uu____6161,src',wl1) ->
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
                 | uu____6275 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6276 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6340  ->
                  fun uu____6341  ->
                    match (uu____6340, uu____6341) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6444 =
                          let uu____6446 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6446
                           in
                        if uu____6444
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6480 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6480
                           then
                             let uu____6497 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6497)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6276 with | (isect,uu____6547) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6583 'Auu____6584 .
    (FStar_Syntax_Syntax.bv * 'Auu____6583) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6584) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6642  ->
              fun uu____6643  ->
                match (uu____6642, uu____6643) with
                | ((a,uu____6662),(b,uu____6664)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6680 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6680) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6711  ->
           match uu____6711 with
           | (y,uu____6718) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6728 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6728) Prims.list ->
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
                   let uu____6890 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6890
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6923 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6975 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7019 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7040 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7048  ->
    match uu___22_7048 with
    | MisMatch (d1,d2) ->
        let uu____7060 =
          let uu____7062 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7064 =
            let uu____7066 =
              let uu____7068 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7068 ")"  in
            Prims.op_Hat ") (" uu____7066  in
          Prims.op_Hat uu____7062 uu____7064  in
        Prims.op_Hat "MisMatch (" uu____7060
    | HeadMatch u ->
        let uu____7075 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7075
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7084  ->
    match uu___23_7084 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7101 -> HeadMatch false
  
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
          let uu____7123 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7123 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7134 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7158 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7168 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7187 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7187
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7188 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7189 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7190 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7203 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7217 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7241) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7247,uu____7248) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7290) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7315;
             FStar_Syntax_Syntax.index = uu____7316;
             FStar_Syntax_Syntax.sort = t2;_},uu____7318)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7326 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7327 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7328 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7343 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7350 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7370 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7370
  
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
           { FStar_Syntax_Syntax.blob = uu____7389;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7390;
             FStar_Syntax_Syntax.ltyp = uu____7391;
             FStar_Syntax_Syntax.rng = uu____7392;_},uu____7393)
            ->
            let uu____7404 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7404 t21
        | (uu____7405,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7406;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7407;
             FStar_Syntax_Syntax.ltyp = uu____7408;
             FStar_Syntax_Syntax.rng = uu____7409;_})
            ->
            let uu____7420 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7420
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7432 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7432
            then FullMatch
            else
              (let uu____7437 =
                 let uu____7446 =
                   let uu____7449 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7449  in
                 let uu____7450 =
                   let uu____7453 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7453  in
                 (uu____7446, uu____7450)  in
               MisMatch uu____7437)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7459),FStar_Syntax_Syntax.Tm_uinst (g,uu____7461)) ->
            let uu____7470 = head_matches env f g  in
            FStar_All.pipe_right uu____7470 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7471) -> HeadMatch true
        | (uu____7473,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7477 = FStar_Const.eq_const c d  in
            if uu____7477
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7487),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7489)) ->
            let uu____7522 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7522
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7532),FStar_Syntax_Syntax.Tm_refine (y,uu____7534)) ->
            let uu____7543 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7543 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7545),uu____7546) ->
            let uu____7551 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7551 head_match
        | (uu____7552,FStar_Syntax_Syntax.Tm_refine (x,uu____7554)) ->
            let uu____7559 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7559 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7560,FStar_Syntax_Syntax.Tm_type
           uu____7561) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7563,FStar_Syntax_Syntax.Tm_arrow uu____7564) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7595),FStar_Syntax_Syntax.Tm_app (head',uu____7597))
            ->
            let uu____7646 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7646 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7648),uu____7649) ->
            let uu____7674 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7674 head_match
        | (uu____7675,FStar_Syntax_Syntax.Tm_app (head1,uu____7677)) ->
            let uu____7702 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7702 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7703,FStar_Syntax_Syntax.Tm_let
           uu____7704) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7732,FStar_Syntax_Syntax.Tm_match uu____7733) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7779,FStar_Syntax_Syntax.Tm_abs
           uu____7780) -> HeadMatch true
        | uu____7818 ->
            let uu____7823 =
              let uu____7832 = delta_depth_of_term env t11  in
              let uu____7835 = delta_depth_of_term env t21  in
              (uu____7832, uu____7835)  in
            MisMatch uu____7823
  
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
              let uu____7904 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7904  in
            (let uu____7906 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7906
             then
               let uu____7911 = FStar_Syntax_Print.term_to_string t  in
               let uu____7913 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7911 uu____7913
             else ());
            (let uu____7918 =
               let uu____7919 = FStar_Syntax_Util.un_uinst head1  in
               uu____7919.FStar_Syntax_Syntax.n  in
             match uu____7918 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7925 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7925 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7939 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7939
                        then
                          let uu____7944 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7944
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7949 ->
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
                      let uu____7967 =
                        let uu____7969 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7969 = FStar_Syntax_Util.Equal  in
                      if uu____7967
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7976 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7976
                          then
                            let uu____7981 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7983 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7981
                              uu____7983
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7988 -> FStar_Pervasives_Native.None)
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
            (let uu____8140 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8140
             then
               let uu____8145 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8147 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8149 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8145
                 uu____8147 uu____8149
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8177 =
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
               match uu____8177 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8225 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8225 with
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
                  uu____8263),uu____8264)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8285 =
                      let uu____8294 = maybe_inline t11  in
                      let uu____8297 = maybe_inline t21  in
                      (uu____8294, uu____8297)  in
                    match uu____8285 with
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
                 (uu____8340,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8341))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8362 =
                      let uu____8371 = maybe_inline t11  in
                      let uu____8374 = maybe_inline t21  in
                      (uu____8371, uu____8374)  in
                    match uu____8362 with
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
             | MisMatch uu____8429 -> fail1 n_delta r t11 t21
             | uu____8438 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8453 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8453
           then
             let uu____8458 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8460 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8462 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8470 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8487 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8487
                    (fun uu____8522  ->
                       match uu____8522 with
                       | (t11,t21) ->
                           let uu____8530 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8532 =
                             let uu____8534 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8534  in
                           Prims.op_Hat uu____8530 uu____8532))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8458 uu____8460 uu____8462 uu____8470
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8551 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8551 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8566  ->
    match uu___24_8566 with
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
      let uu___1212_8615 = p  in
      let uu____8618 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8619 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1212_8615.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8618;
        FStar_TypeChecker_Common.relation =
          (uu___1212_8615.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8619;
        FStar_TypeChecker_Common.element =
          (uu___1212_8615.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1212_8615.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1212_8615.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1212_8615.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1212_8615.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1212_8615.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8634 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8634
            (fun _8639  -> FStar_TypeChecker_Common.TProb _8639)
      | FStar_TypeChecker_Common.CProb uu____8640 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8663 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8663 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8671 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8671 with
           | (lh,lhs_args) ->
               let uu____8718 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8718 with
                | (rh,rhs_args) ->
                    let uu____8765 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8778,FStar_Syntax_Syntax.Tm_uvar uu____8779)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8868 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8895,uu____8896)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8911,FStar_Syntax_Syntax.Tm_uvar uu____8912)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8927,FStar_Syntax_Syntax.Tm_arrow uu____8928)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1263_8958 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1263_8958.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1263_8958.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1263_8958.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1263_8958.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1263_8958.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1263_8958.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1263_8958.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1263_8958.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1263_8958.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8961,FStar_Syntax_Syntax.Tm_type uu____8962)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1263_8978 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1263_8978.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1263_8978.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1263_8978.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1263_8978.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1263_8978.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1263_8978.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1263_8978.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1263_8978.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1263_8978.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8981,FStar_Syntax_Syntax.Tm_uvar uu____8982)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1263_8998 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1263_8998.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1263_8998.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1263_8998.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1263_8998.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1263_8998.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1263_8998.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1263_8998.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1263_8998.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1263_8998.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9001,FStar_Syntax_Syntax.Tm_uvar uu____9002)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9017,uu____9018)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9033,FStar_Syntax_Syntax.Tm_uvar uu____9034)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9049,uu____9050) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8765 with
                     | (rank,tp1) ->
                         let uu____9063 =
                           FStar_All.pipe_right
                             (let uu___1283_9067 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1283_9067.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1283_9067.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1283_9067.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1283_9067.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1283_9067.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1283_9067.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1283_9067.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1283_9067.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1283_9067.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9070  ->
                                FStar_TypeChecker_Common.TProb _9070)
                            in
                         (rank, uu____9063))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9074 =
            FStar_All.pipe_right
              (let uu___1287_9078 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1287_9078.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1287_9078.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1287_9078.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1287_9078.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1287_9078.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1287_9078.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1287_9078.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1287_9078.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1287_9078.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9081  -> FStar_TypeChecker_Common.CProb _9081)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9074)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9141 probs =
      match uu____9141 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9222 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9243 = rank wl.tcenv hd1  in
               (match uu____9243 with
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
                      (let uu____9304 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9309 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9309)
                          in
                       if uu____9304
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
          let uu____9382 = FStar_Syntax_Util.head_and_args t  in
          match uu____9382 with
          | (hd1,uu____9401) ->
              let uu____9426 =
                let uu____9427 = FStar_Syntax_Subst.compress hd1  in
                uu____9427.FStar_Syntax_Syntax.n  in
              (match uu____9426 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9432) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9467  ->
                           match uu____9467 with
                           | (y,uu____9476) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9499  ->
                                       match uu____9499 with
                                       | (x,uu____9508) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9513 -> false)
           in
        let uu____9515 = rank tcenv p  in
        match uu____9515 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9524 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9605 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9624 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9643 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9660 = FStar_Thunk.mkv s  in UFailed uu____9660 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9675 = FStar_Thunk.mk s  in UFailed uu____9675 
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
                        let uu____9727 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9727 with
                        | (k,uu____9735) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9748 -> false)))
            | uu____9750 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9802 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9810 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9810 = Prims.int_zero))
                           in
                        if uu____9802 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9831 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9839 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9839 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9831)
               in
            let uu____9843 = filter1 u12  in
            let uu____9846 = filter1 u22  in (uu____9843, uu____9846)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9881 = filter_out_common_univs us1 us2  in
                   (match uu____9881 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9941 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9941 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9944 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9961  ->
                               let uu____9962 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9964 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9962 uu____9964))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9990 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9990 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10016 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10016 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10019 ->
                   ufailed_thunk
                     (fun uu____10030  ->
                        let uu____10031 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10033 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10031 uu____10033 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10036,uu____10037) ->
              let uu____10039 =
                let uu____10041 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10043 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10041 uu____10043
                 in
              failwith uu____10039
          | (FStar_Syntax_Syntax.U_unknown ,uu____10046) ->
              let uu____10047 =
                let uu____10049 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10051 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10049 uu____10051
                 in
              failwith uu____10047
          | (uu____10054,FStar_Syntax_Syntax.U_bvar uu____10055) ->
              let uu____10057 =
                let uu____10059 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10061 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10059 uu____10061
                 in
              failwith uu____10057
          | (uu____10064,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10065 =
                let uu____10067 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10069 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10067 uu____10069
                 in
              failwith uu____10065
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10099 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10099
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10116 = occurs_univ v1 u3  in
              if uu____10116
              then
                let uu____10119 =
                  let uu____10121 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10123 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10121 uu____10123
                   in
                try_umax_components u11 u21 uu____10119
              else
                (let uu____10128 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10128)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10140 = occurs_univ v1 u3  in
              if uu____10140
              then
                let uu____10143 =
                  let uu____10145 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10147 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10145 uu____10147
                   in
                try_umax_components u11 u21 uu____10143
              else
                (let uu____10152 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10152)
          | (FStar_Syntax_Syntax.U_max uu____10153,uu____10154) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10162 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10162
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10168,FStar_Syntax_Syntax.U_max uu____10169) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10177 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10177
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10183,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10185,FStar_Syntax_Syntax.U_name uu____10186) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10188) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10190) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10192,FStar_Syntax_Syntax.U_succ uu____10193) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10195,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10302 = bc1  in
      match uu____10302 with
      | (bs1,mk_cod1) ->
          let uu____10346 = bc2  in
          (match uu____10346 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10457 = aux xs ys  in
                     (match uu____10457 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10540 =
                       let uu____10547 = mk_cod1 xs  in ([], uu____10547)  in
                     let uu____10550 =
                       let uu____10557 = mk_cod2 ys  in ([], uu____10557)  in
                     (uu____10540, uu____10550)
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
                  let uu____10626 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10626 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10629 =
                    let uu____10630 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10630 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10629
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10635 = has_type_guard t1 t2  in (uu____10635, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10636 = has_type_guard t2 t1  in (uu____10636, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___25_10643  ->
    match uu___25_10643 with
    | Flex (uu____10645,uu____10646,[]) -> true
    | uu____10656 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____10670 = f  in
      match uu____10670 with
      | Flex (uu____10672,u,uu____10674) ->
          (match u.FStar_Syntax_Syntax.ctx_uvar_meta with
           | FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Ctx_uvar_meta_attr a) ->
               let uu____10679 =
                 FStar_TypeChecker_Env.lookup_attr wl.tcenv
                   FStar_Parser_Const.resolve_implicits_attr_string
                  in
               FStar_All.pipe_right uu____10679
                 (FStar_Util.for_some
                    (fun hook  ->
                       FStar_All.pipe_right hook.FStar_Syntax_Syntax.sigattrs
                         (FStar_Util.for_some (FStar_Syntax_Util.attr_eq a))))
           | uu____10691 -> false)
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10718 = f  in
      match uu____10718 with
      | Flex
          (uu____10725,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10726;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10727;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____10730;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____10731;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____10732;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____10733;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10797  ->
                 match uu____10797 with
                 | (y,uu____10806) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10960 =
                  let uu____10975 =
                    let uu____10978 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10978  in
                  ((FStar_List.rev pat_binders), uu____10975)  in
                FStar_Pervasives_Native.Some uu____10960
            | (uu____11011,[]) ->
                let uu____11042 =
                  let uu____11057 =
                    let uu____11060 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11060  in
                  ((FStar_List.rev pat_binders), uu____11057)  in
                FStar_Pervasives_Native.Some uu____11042
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11151 =
                  let uu____11152 = FStar_Syntax_Subst.compress a  in
                  uu____11152.FStar_Syntax_Syntax.n  in
                (match uu____11151 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11172 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11172
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1631_11202 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1631_11202.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1631_11202.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11206 =
                            let uu____11207 =
                              let uu____11214 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11214)  in
                            FStar_Syntax_Syntax.NT uu____11207  in
                          [uu____11206]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1637_11230 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1637_11230.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1637_11230.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11231 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11271 =
                  let uu____11278 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11278  in
                (match uu____11271 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11337 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11362 ->
               let uu____11363 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11363 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11659 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11659
       then
         let uu____11664 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11664
       else ());
      (let uu____11670 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11670
       then
         let uu____11675 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11675
       else ());
      (let uu____11680 = next_prob probs  in
       match uu____11680 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1664_11707 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1664_11707.wl_deferred);
               ctr = (uu___1664_11707.ctr);
               defer_ok = (uu___1664_11707.defer_ok);
               smt_ok = (uu___1664_11707.smt_ok);
               umax_heuristic_ok = (uu___1664_11707.umax_heuristic_ok);
               tcenv = (uu___1664_11707.tcenv);
               wl_implicits = (uu___1664_11707.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11716 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11716
                 then
                   let uu____11719 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11719
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
                       (let uu____11726 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11726)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1676_11732 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1676_11732.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1676_11732.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1676_11732.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1676_11732.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1676_11732.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1676_11732.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1676_11732.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1676_11732.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1676_11732.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11757 ->
                let uu____11767 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11832  ->
                          match uu____11832 with
                          | (c,uu____11842,uu____11843) -> c < probs.ctr))
                   in
                (match uu____11767 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11891 =
                            let uu____11896 =
                              FStar_List.map
                                (fun uu____11917  ->
                                   match uu____11917 with
                                   | (uu____11933,x,y) ->
                                       let uu____11944 = FStar_Thunk.force x
                                          in
                                       (uu____11944, y)) probs.wl_deferred
                               in
                            (uu____11896, (probs.wl_implicits))  in
                          Success uu____11891
                      | uu____11948 ->
                          let uu____11958 =
                            let uu___1694_11959 = probs  in
                            let uu____11960 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11981  ->
                                      match uu____11981 with
                                      | (uu____11989,uu____11990,y) -> y))
                               in
                            {
                              attempting = uu____11960;
                              wl_deferred = rest;
                              ctr = (uu___1694_11959.ctr);
                              defer_ok = (uu___1694_11959.defer_ok);
                              smt_ok = (uu___1694_11959.smt_ok);
                              umax_heuristic_ok =
                                (uu___1694_11959.umax_heuristic_ok);
                              tcenv = (uu___1694_11959.tcenv);
                              wl_implicits = (uu___1694_11959.wl_implicits)
                            }  in
                          solve env uu____11958))))

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
            let uu____11999 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11999 with
            | USolved wl1 ->
                let uu____12001 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12001
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12004 = defer_lit "" orig wl1  in
                solve env uu____12004

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
                  let uu____12055 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12055 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12058 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12071;
                  FStar_Syntax_Syntax.vars = uu____12072;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12075;
                  FStar_Syntax_Syntax.vars = uu____12076;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12089,uu____12090) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12098,FStar_Syntax_Syntax.Tm_uinst uu____12099) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12107 -> USolved wl

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
            ((let uu____12118 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12118
              then
                let uu____12123 = prob_to_string env orig  in
                let uu____12125 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12123 uu____12125
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
               let uu____12218 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12218 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12273 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12273
                then
                  let uu____12278 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12280 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12278 uu____12280
                else ());
               (let uu____12285 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12285 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12331 = eq_prob t1 t2 wl2  in
                         (match uu____12331 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12352 ->
                         let uu____12361 = eq_prob t1 t2 wl2  in
                         (match uu____12361 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12411 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12426 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12427 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12426, uu____12427)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12432 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12433 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12432, uu____12433)
                            in
                         (match uu____12411 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12464 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12464 with
                                | (t1_hd,t1_args) ->
                                    let uu____12509 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12509 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12575 =
                                              let uu____12582 =
                                                let uu____12593 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12593 :: t1_args  in
                                              let uu____12610 =
                                                let uu____12619 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12619 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12668  ->
                                                   fun uu____12669  ->
                                                     fun uu____12670  ->
                                                       match (uu____12668,
                                                               uu____12669,
                                                               uu____12670)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12720),
                                                          (a2,uu____12722))
                                                           ->
                                                           let uu____12759 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12759
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12582
                                                uu____12610
                                               in
                                            match uu____12575 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1848_12785 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1848_12785.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1848_12785.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1848_12785.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12796 =
                                                  solve env1 wl'  in
                                                (match uu____12796 with
                                                 | Success (uu____12799,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1857_12803
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1857_12803.attempting);
                                                            wl_deferred =
                                                              (uu___1857_12803.wl_deferred);
                                                            ctr =
                                                              (uu___1857_12803.ctr);
                                                            defer_ok =
                                                              (uu___1857_12803.defer_ok);
                                                            smt_ok =
                                                              (uu___1857_12803.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1857_12803.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1857_12803.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12804 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12836 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12836 with
                                | (t1_base,p1_opt) ->
                                    let uu____12872 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12872 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12971 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12971
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
                                               let uu____13024 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13024
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
                                               let uu____13056 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13056
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
                                               let uu____13088 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13088
                                           | uu____13091 -> t_base  in
                                         let uu____13108 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13108 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13122 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13122, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13129 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13129 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13165 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13165 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13201 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13201
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
                              let uu____13225 = combine t11 t21 wl2  in
                              (match uu____13225 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13258 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13258
                                     then
                                       let uu____13263 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13263
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13305 ts1 =
               match uu____13305 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13368 = pairwise out t wl2  in
                        (match uu____13368 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13404 =
               let uu____13415 = FStar_List.hd ts  in (uu____13415, [], wl1)
                in
             let uu____13424 = FStar_List.tl ts  in
             aux uu____13404 uu____13424  in
           let uu____13431 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13431 with
           | (this_flex,this_rigid) ->
               let uu____13457 =
                 let uu____13458 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13458.FStar_Syntax_Syntax.n  in
               (match uu____13457 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13483 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13483
                    then
                      let uu____13486 = destruct_flex_t this_flex wl  in
                      (match uu____13486 with
                       | (flex,wl1) ->
                           let uu____13493 = quasi_pattern env flex  in
                           (match uu____13493 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13512 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13512
                                  then
                                    let uu____13517 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13517
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13524 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1959_13527 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1959_13527.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1959_13527.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1959_13527.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1959_13527.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1959_13527.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1959_13527.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1959_13527.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1959_13527.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1959_13527.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13524)
                | uu____13528 ->
                    ((let uu____13530 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13530
                      then
                        let uu____13535 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13535
                      else ());
                     (let uu____13540 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13540 with
                      | (u,_args) ->
                          let uu____13583 =
                            let uu____13584 = FStar_Syntax_Subst.compress u
                               in
                            uu____13584.FStar_Syntax_Syntax.n  in
                          (match uu____13583 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13612 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13612 with
                                 | (u',uu____13631) ->
                                     let uu____13656 =
                                       let uu____13657 = whnf env u'  in
                                       uu____13657.FStar_Syntax_Syntax.n  in
                                     (match uu____13656 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13679 -> false)
                                  in
                               let uu____13681 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13704  ->
                                         match uu___26_13704 with
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
                                              | uu____13718 -> false)
                                         | uu____13722 -> false))
                                  in
                               (match uu____13681 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13737 = whnf env this_rigid
                                         in
                                      let uu____13738 =
                                        FStar_List.collect
                                          (fun uu___27_13744  ->
                                             match uu___27_13744 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13750 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13750]
                                             | uu____13754 -> [])
                                          bounds_probs
                                         in
                                      uu____13737 :: uu____13738  in
                                    let uu____13755 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13755 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13788 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13803 =
                                               let uu____13804 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13804.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13803 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13816 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13816)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13827 -> bound  in
                                           let uu____13828 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13828)  in
                                         (match uu____13788 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13863 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13863
                                                then
                                                  let wl'1 =
                                                    let uu___2019_13869 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2019_13869.wl_deferred);
                                                      ctr =
                                                        (uu___2019_13869.ctr);
                                                      defer_ok =
                                                        (uu___2019_13869.defer_ok);
                                                      smt_ok =
                                                        (uu___2019_13869.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2019_13869.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2019_13869.tcenv);
                                                      wl_implicits =
                                                        (uu___2019_13869.wl_implicits)
                                                    }  in
                                                  let uu____13870 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13870
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13876 =
                                                  solve_t env eq_prob
                                                    (let uu___2024_13878 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2024_13878.wl_deferred);
                                                       ctr =
                                                         (uu___2024_13878.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2024_13878.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2024_13878.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2024_13878.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13876 with
                                                | Success (uu____13880,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2030_13883 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2030_13883.wl_deferred);
                                                        ctr =
                                                          (uu___2030_13883.ctr);
                                                        defer_ok =
                                                          (uu___2030_13883.defer_ok);
                                                        smt_ok =
                                                          (uu___2030_13883.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2030_13883.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2030_13883.tcenv);
                                                        wl_implicits =
                                                          (uu___2030_13883.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2033_13885 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2033_13885.attempting);
                                                        wl_deferred =
                                                          (uu___2033_13885.wl_deferred);
                                                        ctr =
                                                          (uu___2033_13885.ctr);
                                                        defer_ok =
                                                          (uu___2033_13885.defer_ok);
                                                        smt_ok =
                                                          (uu___2033_13885.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2033_13885.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2033_13885.tcenv);
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
                                                    let uu____13901 =
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
                                                    ((let uu____13913 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13913
                                                      then
                                                        let uu____13918 =
                                                          let uu____13920 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13920
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13918
                                                      else ());
                                                     (let uu____13933 =
                                                        let uu____13948 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13948)
                                                         in
                                                      match uu____13933 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13970))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13996 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13996
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
                                                                  let uu____14016
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14016))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14041 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14041
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
                                                                    let uu____14061
                                                                    =
                                                                    let uu____14066
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14066
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14061
                                                                    [] wl2
                                                                     in
                                                                  let uu____14072
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14072))))
                                                      | uu____14073 ->
                                                          let uu____14088 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14088 p)))))))
                           | uu____14095 when flip ->
                               let uu____14096 =
                                 let uu____14098 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14100 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14098 uu____14100
                                  in
                               failwith uu____14096
                           | uu____14103 ->
                               let uu____14104 =
                                 let uu____14106 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14108 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14106 uu____14108
                                  in
                               failwith uu____14104)))))

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
                      (fun uu____14144  ->
                         match uu____14144 with
                         | (x,i) ->
                             let uu____14163 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14163, i)) bs_lhs
                     in
                  let uu____14166 = lhs  in
                  match uu____14166 with
                  | Flex (uu____14167,u_lhs,uu____14169) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14266 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14276 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14276, univ)
                             in
                          match uu____14266 with
                          | (k,univ) ->
                              let uu____14283 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14283 with
                               | (uu____14300,u,wl3) ->
                                   let uu____14303 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14303, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14329 =
                              let uu____14342 =
                                let uu____14353 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14353 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14404  ->
                                   fun uu____14405  ->
                                     match (uu____14404, uu____14405) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14506 =
                                           let uu____14513 =
                                             let uu____14516 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14516
                                              in
                                           copy_uvar u_lhs [] uu____14513 wl2
                                            in
                                         (match uu____14506 with
                                          | (uu____14545,t_a,wl3) ->
                                              let uu____14548 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14548 with
                                               | (uu____14567,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14342
                                ([], wl1)
                               in
                            (match uu____14329 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2145_14623 = ct  in
                                   let uu____14624 =
                                     let uu____14627 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14627
                                      in
                                   let uu____14642 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2145_14623.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2145_14623.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14624;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14642;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2145_14623.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2148_14660 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2148_14660.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2148_14660.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14663 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14663 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14701 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14701 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14712 =
                                          let uu____14717 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14717)  in
                                        TERM uu____14712  in
                                      let uu____14718 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14718 with
                                       | (sub_prob,wl3) ->
                                           let uu____14732 =
                                             let uu____14733 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14733
                                              in
                                           solve env uu____14732))
                             | (x,imp)::formals2 ->
                                 let uu____14755 =
                                   let uu____14762 =
                                     let uu____14765 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14765
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14762 wl1
                                    in
                                 (match uu____14755 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14786 =
                                          let uu____14789 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14789
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14786 u_x
                                         in
                                      let uu____14790 =
                                        let uu____14793 =
                                          let uu____14796 =
                                            let uu____14797 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14797, imp)  in
                                          [uu____14796]  in
                                        FStar_List.append bs_terms
                                          uu____14793
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14790 formals2 wl2)
                              in
                           let uu____14824 = occurs_check u_lhs arrow1  in
                           (match uu____14824 with
                            | (uu____14837,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14853 =
                                    FStar_Thunk.mk
                                      (fun uu____14857  ->
                                         let uu____14858 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14858)
                                     in
                                  giveup_or_defer env orig wl uu____14853
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
              (let uu____14891 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14891
               then
                 let uu____14896 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14899 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14896 (rel_to_string (p_rel orig)) uu____14899
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15030 = rhs wl1 scope env1 subst1  in
                     (match uu____15030 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15053 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15053
                            then
                              let uu____15058 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15058
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15136 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15136 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2218_15138 = hd1  in
                       let uu____15139 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2218_15138.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2218_15138.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15139
                       }  in
                     let hd21 =
                       let uu___2221_15143 = hd2  in
                       let uu____15144 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2221_15143.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2221_15143.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15144
                       }  in
                     let uu____15147 =
                       let uu____15152 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15152
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15147 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15175 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15175
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15182 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15182 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15254 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15254
                                  in
                               ((let uu____15272 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15272
                                 then
                                   let uu____15277 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15279 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15277
                                     uu____15279
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15314 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15350 = aux wl [] env [] bs1 bs2  in
               match uu____15350 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15409 = attempt sub_probs wl2  in
                   solve env1 uu____15409)

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
            let uu___2259_15429 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2259_15429.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2259_15429.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15441 = try_solve env wl'  in
          match uu____15441 with
          | Success (uu____15442,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2268_15446 = wl  in
                  {
                    attempting = (uu___2268_15446.attempting);
                    wl_deferred = (uu___2268_15446.wl_deferred);
                    ctr = (uu___2268_15446.ctr);
                    defer_ok = (uu___2268_15446.defer_ok);
                    smt_ok = (uu___2268_15446.smt_ok);
                    umax_heuristic_ok = (uu___2268_15446.umax_heuristic_ok);
                    tcenv = (uu___2268_15446.tcenv);
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
        (let uu____15455 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15455 wl)

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
              let uu____15469 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15469 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15503 = lhs1  in
              match uu____15503 with
              | Flex (uu____15506,ctx_u,uu____15508) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15516 ->
                        let uu____15517 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15517 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15566 = quasi_pattern env1 lhs1  in
              match uu____15566 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15600) ->
                  let uu____15605 = lhs1  in
                  (match uu____15605 with
                   | Flex (t_lhs,ctx_u,args) ->
                       let uu____15620 = occurs_check ctx_u rhs1  in
                       (match uu____15620 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15671 =
                                let uu____15679 =
                                  let uu____15681 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15681
                                   in
                                FStar_Util.Inl uu____15679  in
                              (uu____15671, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15709 =
                                 let uu____15711 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15711  in
                               if uu____15709
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15738 =
                                    let uu____15746 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15746  in
                                  let uu____15752 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15738, uu____15752)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15796 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15796 with
              | (rhs_hd,args) ->
                  let uu____15839 = FStar_Util.prefix args  in
                  (match uu____15839 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15911 = lhs1  in
                       (match uu____15911 with
                        | Flex (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15915 =
                              let uu____15926 =
                                let uu____15933 =
                                  let uu____15936 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15936
                                   in
                                copy_uvar u_lhs [] uu____15933 wl1  in
                              match uu____15926 with
                              | (uu____15963,t_last_arg,wl2) ->
                                  let uu____15966 =
                                    let uu____15973 =
                                      let uu____15974 =
                                        let uu____15983 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15983]  in
                                      FStar_List.append bs_lhs uu____15974
                                       in
                                    copy_uvar u_lhs uu____15973 t_res_lhs wl2
                                     in
                                  (match uu____15966 with
                                   | (uu____16018,lhs',wl3) ->
                                       let uu____16021 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16021 with
                                        | (uu____16038,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15915 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16059 =
                                     let uu____16060 =
                                       let uu____16065 =
                                         let uu____16066 =
                                           let uu____16069 =
                                             let uu____16074 =
                                               let uu____16075 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16075]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16074
                                              in
                                           uu____16069
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16066
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16065)  in
                                     TERM uu____16060  in
                                   [uu____16059]  in
                                 let uu____16100 =
                                   let uu____16107 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16107 with
                                   | (p1,wl3) ->
                                       let uu____16127 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16127 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16100 with
                                  | (sub_probs,wl3) ->
                                      let uu____16159 =
                                        let uu____16160 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16160  in
                                      solve env1 uu____16159))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16194 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16194 with
                | (uu____16212,args) ->
                    (match args with | [] -> false | uu____16248 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16267 =
                  let uu____16268 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16268.FStar_Syntax_Syntax.n  in
                match uu____16267 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16272 -> true
                | uu____16288 -> false  in
              let uu____16290 = quasi_pattern env1 lhs1  in
              match uu____16290 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16308  ->
                         let uu____16309 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16309)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16318 = is_app rhs1  in
                  if uu____16318
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16323 = is_arrow rhs1  in
                     if uu____16323
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16335  ->
                               let uu____16336 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16336)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16340 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16340
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16346 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16346
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16351 = lhs  in
                (match uu____16351 with
                 | Flex (_t1,ctx_uv,args_lhs) ->
                     let uu____16355 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16355 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16373 =
                              let uu____16377 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16377
                               in
                            FStar_All.pipe_right uu____16373
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16398 = occurs_check ctx_uv rhs1  in
                          (match uu____16398 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16427 =
                                   let uu____16428 =
                                     let uu____16430 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16430
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16428
                                    in
                                 giveup_or_defer env orig wl uu____16427
                               else
                                 (let uu____16438 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16438
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16445 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16445
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16458  ->
                                              let uu____16459 =
                                                names_to_string1 fvs2  in
                                              let uu____16461 =
                                                names_to_string1 fvs1  in
                                              let uu____16463 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16459 uu____16461
                                                uu____16463)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16475 ->
                          if wl.defer_ok
                          then
                            let uu____16479 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16479
                          else
                            (let uu____16484 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16484 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16510 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16510
                             | (FStar_Util.Inl msg,uu____16512) ->
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
                  let uu____16530 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16530
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16536 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16536
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16542 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16542
                else
                  (let uu____16547 =
                     let uu____16564 = quasi_pattern env lhs  in
                     let uu____16571 = quasi_pattern env rhs  in
                     (uu____16564, uu____16571)  in
                   match uu____16547 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16614 = lhs  in
                       (match uu____16614 with
                        | Flex
                            ({ FStar_Syntax_Syntax.n = uu____16615;
                               FStar_Syntax_Syntax.pos = range;
                               FStar_Syntax_Syntax.vars = uu____16617;_},u_lhs,uu____16619)
                            ->
                            let uu____16622 = rhs  in
                            (match uu____16622 with
                             | Flex (uu____16623,u_rhs,uu____16625) ->
                                 let uu____16626 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16626
                                 then
                                   let uu____16633 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16633
                                 else
                                   (let uu____16636 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16636 with
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
                                        let uu____16668 =
                                          let uu____16675 =
                                            let uu____16678 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16678
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16675
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16668 with
                                         | (uu____16684,w,wl1) ->
                                             let w_app =
                                               let uu____16690 =
                                                 let uu____16695 =
                                                   FStar_List.map
                                                     (fun uu____16706  ->
                                                        match uu____16706
                                                        with
                                                        | (z,uu____16714) ->
                                                            let uu____16719 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16719) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16695
                                                  in
                                               uu____16690
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16721 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16721
                                               then
                                                 let uu____16726 =
                                                   let uu____16730 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16732 =
                                                     let uu____16736 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16738 =
                                                       let uu____16742 =
                                                         term_to_string w  in
                                                       let uu____16744 =
                                                         let uu____16748 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16757 =
                                                           let uu____16761 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16770 =
                                                             let uu____16774
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16774]
                                                              in
                                                           uu____16761 ::
                                                             uu____16770
                                                            in
                                                         uu____16748 ::
                                                           uu____16757
                                                          in
                                                       uu____16742 ::
                                                         uu____16744
                                                        in
                                                     uu____16736 ::
                                                       uu____16738
                                                      in
                                                   uu____16730 :: uu____16732
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16726
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16791 =
                                                     let uu____16796 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16796)  in
                                                   TERM uu____16791  in
                                                 let uu____16797 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16797
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16805 =
                                                        let uu____16810 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16810)
                                                         in
                                                      TERM uu____16805  in
                                                    [s1; s2])
                                                  in
                                               let uu____16811 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16811))))))
                   | uu____16812 ->
                       let uu____16829 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16829)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16883 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16883
            then
              let uu____16888 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16890 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16892 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16894 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16888 uu____16890 uu____16892 uu____16894
            else ());
           (let uu____16905 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16905 with
            | (head1,args1) ->
                let uu____16948 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16948 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17018 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17018 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17023 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17023)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17044 =
                         FStar_Thunk.mk
                           (fun uu____17051  ->
                              let uu____17052 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17054 = args_to_string args1  in
                              let uu____17058 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17060 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17052 uu____17054 uu____17058
                                uu____17060)
                          in
                       giveup env1 uu____17044 orig
                     else
                       (let uu____17067 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17072 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17072 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17067
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2530_17076 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2530_17076.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2530_17076.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2530_17076.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2530_17076.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2530_17076.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2530_17076.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2530_17076.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2530_17076.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17086 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17086
                                    else solve env1 wl2))
                        else
                          (let uu____17091 = base_and_refinement env1 t1  in
                           match uu____17091 with
                           | (base1,refinement1) ->
                               let uu____17116 = base_and_refinement env1 t2
                                  in
                               (match uu____17116 with
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
                                           let uu____17281 =
                                             FStar_List.fold_right
                                               (fun uu____17321  ->
                                                  fun uu____17322  ->
                                                    match (uu____17321,
                                                            uu____17322)
                                                    with
                                                    | (((a1,uu____17374),
                                                        (a2,uu____17376)),
                                                       (probs,wl3)) ->
                                                        let uu____17425 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17425
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17281 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17468 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17468
                                                 then
                                                   let uu____17473 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17473
                                                 else ());
                                                (let uu____17479 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17479
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
                                                    (let uu____17506 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17506 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17522 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17522
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17530 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17530))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17555 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17555 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17571 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17571
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17579 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17579)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17607 =
                                           match uu____17607 with
                                           | (prob,reason) ->
                                               ((let uu____17624 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17624
                                                 then
                                                   let uu____17629 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17631 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17633 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17629 uu____17631
                                                     uu____17633
                                                 else ());
                                                (let uu____17639 =
                                                   let uu____17648 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17651 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17648, uu____17651)
                                                    in
                                                 match uu____17639 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17664 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17664 with
                                                      | (head1',uu____17682)
                                                          ->
                                                          let uu____17707 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17707
                                                           with
                                                           | (head2',uu____17725)
                                                               ->
                                                               let uu____17750
                                                                 =
                                                                 let uu____17755
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17756
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17755,
                                                                   uu____17756)
                                                                  in
                                                               (match uu____17750
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17758
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17758
                                                                    then
                                                                    let uu____17763
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17765
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17767
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17769
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17763
                                                                    uu____17765
                                                                    uu____17767
                                                                    uu____17769
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17774
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2618_17782
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2618_17782.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17784
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17784
                                                                    then
                                                                    let uu____17789
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17789
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17794 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17806 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17806 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17814 =
                                             let uu____17815 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17815.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17814 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17820 -> false  in
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
                                          | uu____17823 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17826 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2638_17862 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2638_17862.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2638_17862.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2638_17862.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2638_17862.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2638_17862.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2638_17862.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2638_17862.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2638_17862.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17938 = destruct_flex_t scrutinee wl1  in
             match uu____17938 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____17949 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17949 with
                  | (xs,pat_term,uu____17965,uu____17966) ->
                      let uu____17971 =
                        FStar_List.fold_left
                          (fun uu____17994  ->
                             fun x  ->
                               match uu____17994 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18015 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18015 with
                                    | (uu____18034,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17971 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18055 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18055 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2679_18072 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2679_18072.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2679_18072.umax_heuristic_ok);
                                    tcenv = (uu___2679_18072.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18083 = solve env1 wl'  in
                                (match uu____18083 with
                                 | Success (uu____18086,imps) ->
                                     let wl'1 =
                                       let uu___2687_18089 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2687_18089.wl_deferred);
                                         ctr = (uu___2687_18089.ctr);
                                         defer_ok =
                                           (uu___2687_18089.defer_ok);
                                         smt_ok = (uu___2687_18089.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2687_18089.umax_heuristic_ok);
                                         tcenv = (uu___2687_18089.tcenv);
                                         wl_implicits =
                                           (uu___2687_18089.wl_implicits)
                                       }  in
                                     let uu____18090 = solve env1 wl'1  in
                                     (match uu____18090 with
                                      | Success (uu____18093,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2695_18097 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2695_18097.attempting);
                                                 wl_deferred =
                                                   (uu___2695_18097.wl_deferred);
                                                 ctr = (uu___2695_18097.ctr);
                                                 defer_ok =
                                                   (uu___2695_18097.defer_ok);
                                                 smt_ok =
                                                   (uu___2695_18097.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2695_18097.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2695_18097.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18098 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18104 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18127 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18127
                 then
                   let uu____18132 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18134 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18132 uu____18134
                 else ());
                (let uu____18139 =
                   let uu____18160 =
                     let uu____18169 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18169)  in
                   let uu____18176 =
                     let uu____18185 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18185)  in
                   (uu____18160, uu____18176)  in
                 match uu____18139 with
                 | ((uu____18215,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18218;
                                   FStar_Syntax_Syntax.vars = uu____18219;_}),
                    (s,t)) ->
                     let uu____18290 =
                       let uu____18292 = is_flex scrutinee  in
                       Prims.op_Negation uu____18292  in
                     if uu____18290
                     then
                       ((let uu____18303 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18303
                         then
                           let uu____18308 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18308
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18327 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18327
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18342 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18342
                           then
                             let uu____18347 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18349 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18347 uu____18349
                           else ());
                          (let pat_discriminates uu___28_18374 =
                             match uu___28_18374 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18390;
                                  FStar_Syntax_Syntax.p = uu____18391;_},FStar_Pervasives_Native.None
                                ,uu____18392) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18406;
                                  FStar_Syntax_Syntax.p = uu____18407;_},FStar_Pervasives_Native.None
                                ,uu____18408) -> true
                             | uu____18435 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18538 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18538 with
                                       | (uu____18540,uu____18541,t') ->
                                           let uu____18559 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18559 with
                                            | (FullMatch ,uu____18571) ->
                                                true
                                            | (HeadMatch
                                               uu____18585,uu____18586) ->
                                                true
                                            | uu____18601 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18638 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18638
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18649 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18649 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18737,uu____18738) ->
                                       branches1
                                   | uu____18883 -> branches  in
                                 let uu____18938 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18947 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18947 with
                                        | (p,uu____18951,uu____18952) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _18981  -> FStar_Util.Inr _18981)
                                   uu____18938))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19011 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19011 with
                                | (p,uu____19020,e) ->
                                    ((let uu____19039 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19039
                                      then
                                        let uu____19044 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19046 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19044 uu____19046
                                      else ());
                                     (let uu____19051 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19066  -> FStar_Util.Inr _19066)
                                        uu____19051)))))
                 | ((s,t),(uu____19069,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19072;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19073;_}))
                     ->
                     let uu____19142 =
                       let uu____19144 = is_flex scrutinee  in
                       Prims.op_Negation uu____19144  in
                     if uu____19142
                     then
                       ((let uu____19155 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19155
                         then
                           let uu____19160 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19160
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19179 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19179
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19194 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19194
                           then
                             let uu____19199 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19201 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19199 uu____19201
                           else ());
                          (let pat_discriminates uu___28_19226 =
                             match uu___28_19226 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19242;
                                  FStar_Syntax_Syntax.p = uu____19243;_},FStar_Pervasives_Native.None
                                ,uu____19244) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19258;
                                  FStar_Syntax_Syntax.p = uu____19259;_},FStar_Pervasives_Native.None
                                ,uu____19260) -> true
                             | uu____19287 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19390 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19390 with
                                       | (uu____19392,uu____19393,t') ->
                                           let uu____19411 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19411 with
                                            | (FullMatch ,uu____19423) ->
                                                true
                                            | (HeadMatch
                                               uu____19437,uu____19438) ->
                                                true
                                            | uu____19453 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19490 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19490
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19501 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19501 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19589,uu____19590) ->
                                       branches1
                                   | uu____19735 -> branches  in
                                 let uu____19790 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19799 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19799 with
                                        | (p,uu____19803,uu____19804) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19833  -> FStar_Util.Inr _19833)
                                   uu____19790))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19863 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19863 with
                                | (p,uu____19872,e) ->
                                    ((let uu____19891 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19891
                                      then
                                        let uu____19896 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19898 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19896 uu____19898
                                      else ());
                                     (let uu____19903 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19918  -> FStar_Util.Inr _19918)
                                        uu____19903)))))
                 | uu____19919 ->
                     ((let uu____19941 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19941
                       then
                         let uu____19946 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19948 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19946 uu____19948
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____19994 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____19994
            then
              let uu____19999 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20001 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20003 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20005 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____19999 uu____20001 uu____20003 uu____20005
            else ());
           (let uu____20010 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20010 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20041,uu____20042) ->
                     let rec may_relate head3 =
                       let uu____20070 =
                         let uu____20071 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20071.FStar_Syntax_Syntax.n  in
                       match uu____20070 with
                       | FStar_Syntax_Syntax.Tm_name uu____20075 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20077 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20102 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20102 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20104 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20107
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20108 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20111,uu____20112) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20154) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20160) ->
                           may_relate t
                       | uu____20165 -> false  in
                     let uu____20167 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20167 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20180 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20180
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20190 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20190
                          then
                            let uu____20193 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20193 with
                             | (guard,wl2) ->
                                 let uu____20200 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20200)
                          else
                            (let uu____20203 =
                               FStar_Thunk.mk
                                 (fun uu____20210  ->
                                    let uu____20211 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20213 =
                                      let uu____20215 =
                                        let uu____20219 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20219
                                          (fun x  ->
                                             let uu____20226 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20226)
                                         in
                                      FStar_Util.dflt "" uu____20215  in
                                    let uu____20231 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20233 =
                                      let uu____20235 =
                                        let uu____20239 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20239
                                          (fun x  ->
                                             let uu____20246 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20246)
                                         in
                                      FStar_Util.dflt "" uu____20235  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20211 uu____20213 uu____20231
                                      uu____20233)
                                in
                             giveup env1 uu____20203 orig))
                 | (HeadMatch (true ),uu____20252) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20267 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20267 with
                        | (guard,wl2) ->
                            let uu____20274 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20274)
                     else
                       (let uu____20277 =
                          FStar_Thunk.mk
                            (fun uu____20282  ->
                               let uu____20283 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20285 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20283 uu____20285)
                           in
                        giveup env1 uu____20277 orig)
                 | (uu____20288,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2870_20302 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2870_20302.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2870_20302.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2870_20302.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2870_20302.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2870_20302.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2870_20302.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2870_20302.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2870_20302.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20329 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20329
          then
            let uu____20332 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20332
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20338 =
                let uu____20341 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20341  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20338 t1);
             (let uu____20360 =
                let uu____20363 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20363  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20360 t2);
             (let uu____20382 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20382
              then
                let uu____20386 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20388 =
                  let uu____20390 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20392 =
                    let uu____20394 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20394  in
                  Prims.op_Hat uu____20390 uu____20392  in
                let uu____20397 =
                  let uu____20399 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20401 =
                    let uu____20403 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20403  in
                  Prims.op_Hat uu____20399 uu____20401  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20386 uu____20388 uu____20397
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20410,uu____20411) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20427,FStar_Syntax_Syntax.Tm_delayed uu____20428) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20444,uu____20445) ->
                  let uu____20472 =
                    let uu___2901_20473 = problem  in
                    let uu____20474 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2901_20473.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20474;
                      FStar_TypeChecker_Common.relation =
                        (uu___2901_20473.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2901_20473.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2901_20473.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2901_20473.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2901_20473.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2901_20473.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2901_20473.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2901_20473.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20472 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20475,uu____20476) ->
                  let uu____20483 =
                    let uu___2907_20484 = problem  in
                    let uu____20485 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2907_20484.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20485;
                      FStar_TypeChecker_Common.relation =
                        (uu___2907_20484.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2907_20484.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2907_20484.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2907_20484.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2907_20484.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2907_20484.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2907_20484.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2907_20484.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20483 wl
              | (uu____20486,FStar_Syntax_Syntax.Tm_ascribed uu____20487) ->
                  let uu____20514 =
                    let uu___2913_20515 = problem  in
                    let uu____20516 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2913_20515.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2913_20515.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2913_20515.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20516;
                      FStar_TypeChecker_Common.element =
                        (uu___2913_20515.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2913_20515.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2913_20515.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2913_20515.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2913_20515.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2913_20515.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20514 wl
              | (uu____20517,FStar_Syntax_Syntax.Tm_meta uu____20518) ->
                  let uu____20525 =
                    let uu___2919_20526 = problem  in
                    let uu____20527 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2919_20526.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2919_20526.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2919_20526.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20527;
                      FStar_TypeChecker_Common.element =
                        (uu___2919_20526.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2919_20526.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2919_20526.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2919_20526.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2919_20526.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2919_20526.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20525 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20529),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20531)) ->
                  let uu____20540 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20540
              | (FStar_Syntax_Syntax.Tm_bvar uu____20541,uu____20542) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20544,FStar_Syntax_Syntax.Tm_bvar uu____20545) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20615 =
                    match uu___29_20615 with
                    | [] -> c
                    | bs ->
                        let uu____20643 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20643
                     in
                  let uu____20654 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20654 with
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
                                    let uu____20803 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20803
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
                  let mk_t t l uu___30_20892 =
                    match uu___30_20892 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20934 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20934 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21079 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21080 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21079
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21080 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21082,uu____21083) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21114 -> true
                    | uu____21134 -> false  in
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
                      (let uu____21194 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3021_21202 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3021_21202.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3021_21202.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3021_21202.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3021_21202.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3021_21202.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3021_21202.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3021_21202.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3021_21202.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3021_21202.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3021_21202.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3021_21202.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3021_21202.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3021_21202.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3021_21202.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3021_21202.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3021_21202.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3021_21202.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3021_21202.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3021_21202.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3021_21202.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3021_21202.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3021_21202.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3021_21202.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3021_21202.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3021_21202.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3021_21202.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3021_21202.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3021_21202.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3021_21202.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3021_21202.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3021_21202.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3021_21202.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3021_21202.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3021_21202.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3021_21202.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3021_21202.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3021_21202.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3021_21202.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3021_21202.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3021_21202.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3021_21202.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3021_21202.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3021_21202.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3021_21202.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21194 with
                       | (uu____21207,ty,uu____21209) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21218 =
                                 let uu____21219 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21219.FStar_Syntax_Syntax.n  in
                               match uu____21218 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21222 ->
                                   let uu____21229 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21229
                               | uu____21230 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21233 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21233
                             then
                               let uu____21238 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21240 =
                                 let uu____21242 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21242
                                  in
                               let uu____21243 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21238 uu____21240 uu____21243
                             else ());
                            r1))
                     in
                  let uu____21248 =
                    let uu____21265 = maybe_eta t1  in
                    let uu____21272 = maybe_eta t2  in
                    (uu____21265, uu____21272)  in
                  (match uu____21248 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3042_21314 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3042_21314.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3042_21314.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3042_21314.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3042_21314.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3042_21314.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3042_21314.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3042_21314.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3042_21314.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21335 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21335
                       then
                         let uu____21338 = destruct_flex_t not_abs wl  in
                         (match uu____21338 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3059_21355 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3059_21355.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3059_21355.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3059_21355.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3059_21355.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3059_21355.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3059_21355.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3059_21355.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3059_21355.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21358 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21358 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21381 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21381
                       then
                         let uu____21384 = destruct_flex_t not_abs wl  in
                         (match uu____21384 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3059_21401 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3059_21401.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3059_21401.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3059_21401.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3059_21401.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3059_21401.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3059_21401.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3059_21401.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3059_21401.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21404 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21404 orig))
                   | uu____21407 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21425,FStar_Syntax_Syntax.Tm_abs uu____21426) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21457 -> true
                    | uu____21477 -> false  in
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
                      (let uu____21537 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3021_21545 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3021_21545.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3021_21545.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3021_21545.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3021_21545.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3021_21545.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3021_21545.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3021_21545.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3021_21545.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3021_21545.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3021_21545.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3021_21545.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3021_21545.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3021_21545.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3021_21545.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3021_21545.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3021_21545.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3021_21545.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3021_21545.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3021_21545.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3021_21545.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3021_21545.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3021_21545.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3021_21545.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3021_21545.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3021_21545.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3021_21545.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3021_21545.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3021_21545.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3021_21545.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3021_21545.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3021_21545.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3021_21545.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3021_21545.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3021_21545.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3021_21545.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3021_21545.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3021_21545.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3021_21545.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3021_21545.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3021_21545.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3021_21545.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3021_21545.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3021_21545.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3021_21545.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21537 with
                       | (uu____21550,ty,uu____21552) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21561 =
                                 let uu____21562 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21562.FStar_Syntax_Syntax.n  in
                               match uu____21561 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21565 ->
                                   let uu____21572 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21572
                               | uu____21573 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21576 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21576
                             then
                               let uu____21581 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21583 =
                                 let uu____21585 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21585
                                  in
                               let uu____21586 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21581 uu____21583 uu____21586
                             else ());
                            r1))
                     in
                  let uu____21591 =
                    let uu____21608 = maybe_eta t1  in
                    let uu____21615 = maybe_eta t2  in
                    (uu____21608, uu____21615)  in
                  (match uu____21591 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3042_21657 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3042_21657.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3042_21657.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3042_21657.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3042_21657.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3042_21657.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3042_21657.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3042_21657.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3042_21657.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21678 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21678
                       then
                         let uu____21681 = destruct_flex_t not_abs wl  in
                         (match uu____21681 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3059_21698 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3059_21698.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3059_21698.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3059_21698.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3059_21698.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3059_21698.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3059_21698.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3059_21698.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3059_21698.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21701 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21701 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21724 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21724
                       then
                         let uu____21727 = destruct_flex_t not_abs wl  in
                         (match uu____21727 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3059_21744 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3059_21744.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3059_21744.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3059_21744.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3059_21744.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3059_21744.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3059_21744.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3059_21744.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3059_21744.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21747 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21747 orig))
                   | uu____21750 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21780 =
                    let uu____21785 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21785 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3082_21813 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3082_21813.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3082_21813.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3084_21815 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3084_21815.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3084_21815.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21816,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3082_21831 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3082_21831.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3082_21831.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3084_21833 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3084_21833.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3084_21833.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21834 -> (x1, x2)  in
                  (match uu____21780 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21853 = as_refinement false env t11  in
                       (match uu____21853 with
                        | (x12,phi11) ->
                            let uu____21861 = as_refinement false env t21  in
                            (match uu____21861 with
                             | (x22,phi21) ->
                                 ((let uu____21870 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21870
                                   then
                                     ((let uu____21875 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21877 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21879 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21875
                                         uu____21877 uu____21879);
                                      (let uu____21882 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21884 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21886 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21882
                                         uu____21884 uu____21886))
                                   else ());
                                  (let uu____21891 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21891 with
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
                                         let uu____21962 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21962
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21974 =
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
                                         (let uu____21987 =
                                            let uu____21990 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____21990
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____21987
                                            (p_guard base_prob));
                                         (let uu____22009 =
                                            let uu____22012 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22012
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22009
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22031 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22031)
                                          in
                                       let has_uvars =
                                         (let uu____22036 =
                                            let uu____22038 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22038
                                             in
                                          Prims.op_Negation uu____22036) ||
                                           (let uu____22042 =
                                              let uu____22044 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22044
                                               in
                                            Prims.op_Negation uu____22042)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22048 =
                                           let uu____22053 =
                                             let uu____22062 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22062]  in
                                           mk_t_problem wl1 uu____22053 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22048 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22085 =
                                                solve env1
                                                  (let uu___3127_22087 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3127_22087.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3127_22087.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3127_22087.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3127_22087.tcenv);
                                                     wl_implicits =
                                                       (uu___3127_22087.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22085 with
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
                                               | Success uu____22102 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22111 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22111
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3140_22120 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3140_22120.attempting);
                                                         wl_deferred =
                                                           (uu___3140_22120.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3140_22120.defer_ok);
                                                         smt_ok =
                                                           (uu___3140_22120.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3140_22120.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3140_22120.tcenv);
                                                         wl_implicits =
                                                           (uu___3140_22120.wl_implicits)
                                                       }  in
                                                     let uu____22122 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22122))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22125,FStar_Syntax_Syntax.Tm_uvar uu____22126) ->
                  let uu____22151 = destruct_flex_t t1 wl  in
                  (match uu____22151 with
                   | (f1,wl1) ->
                       let uu____22158 = destruct_flex_t t2 wl1  in
                       (match uu____22158 with
                        | (f2,wl2) ->
                            let uu____22165 =
                              (should_defer_flex_to_user_tac wl2 f1) ||
                                (should_defer_flex_to_user_tac wl2 f1)
                               in
                            if uu____22165
                            then
                              let uu____22168 =
                                FStar_Thunk.mkv "Deferring to user tactic"
                                 in
                              giveup_or_defer1
                                (FStar_TypeChecker_Common.TProb problem)
                                uu____22168
                            else solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22173;
                    FStar_Syntax_Syntax.pos = uu____22174;
                    FStar_Syntax_Syntax.vars = uu____22175;_},uu____22176),FStar_Syntax_Syntax.Tm_uvar
                 uu____22177) ->
                  let uu____22226 = destruct_flex_t t1 wl  in
                  (match uu____22226 with
                   | (f1,wl1) ->
                       let uu____22233 = destruct_flex_t t2 wl1  in
                       (match uu____22233 with
                        | (f2,wl2) ->
                            let uu____22240 =
                              (should_defer_flex_to_user_tac wl2 f1) ||
                                (should_defer_flex_to_user_tac wl2 f1)
                               in
                            if uu____22240
                            then
                              let uu____22243 =
                                FStar_Thunk.mkv "Deferring to user tactic"
                                 in
                              giveup_or_defer1
                                (FStar_TypeChecker_Common.TProb problem)
                                uu____22243
                            else solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22248,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22249;
                    FStar_Syntax_Syntax.pos = uu____22250;
                    FStar_Syntax_Syntax.vars = uu____22251;_},uu____22252))
                  ->
                  let uu____22301 = destruct_flex_t t1 wl  in
                  (match uu____22301 with
                   | (f1,wl1) ->
                       let uu____22308 = destruct_flex_t t2 wl1  in
                       (match uu____22308 with
                        | (f2,wl2) ->
                            let uu____22315 =
                              (should_defer_flex_to_user_tac wl2 f1) ||
                                (should_defer_flex_to_user_tac wl2 f1)
                               in
                            if uu____22315
                            then
                              let uu____22318 =
                                FStar_Thunk.mkv "Deferring to user tactic"
                                 in
                              giveup_or_defer1
                                (FStar_TypeChecker_Common.TProb problem)
                                uu____22318
                            else solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22323;
                    FStar_Syntax_Syntax.pos = uu____22324;
                    FStar_Syntax_Syntax.vars = uu____22325;_},uu____22326),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22327;
                    FStar_Syntax_Syntax.pos = uu____22328;
                    FStar_Syntax_Syntax.vars = uu____22329;_},uu____22330))
                  ->
                  let uu____22403 = destruct_flex_t t1 wl  in
                  (match uu____22403 with
                   | (f1,wl1) ->
                       let uu____22410 = destruct_flex_t t2 wl1  in
                       (match uu____22410 with
                        | (f2,wl2) ->
                            let uu____22417 =
                              (should_defer_flex_to_user_tac wl2 f1) ||
                                (should_defer_flex_to_user_tac wl2 f1)
                               in
                            if uu____22417
                            then
                              let uu____22420 =
                                FStar_Thunk.mkv "Deferring to user tactic"
                                 in
                              giveup_or_defer1
                                (FStar_TypeChecker_Common.TProb problem)
                                uu____22420
                            else solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22425,uu____22426) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22439 = destruct_flex_t t1 wl  in
                  (match uu____22439 with
                   | (f1,wl1) ->
                       let uu____22446 = should_defer_flex_to_user_tac wl1 f1
                          in
                       if uu____22446
                       then
                         let uu____22449 =
                           FStar_Thunk.mkv "Deferring to user tactic"  in
                         giveup_or_defer1
                           (FStar_TypeChecker_Common.TProb problem)
                           uu____22449
                       else solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22454;
                    FStar_Syntax_Syntax.pos = uu____22455;
                    FStar_Syntax_Syntax.vars = uu____22456;_},uu____22457),uu____22458)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22495 = destruct_flex_t t1 wl  in
                  (match uu____22495 with
                   | (f1,wl1) ->
                       let uu____22502 = should_defer_flex_to_user_tac wl1 f1
                          in
                       if uu____22502
                       then
                         let uu____22505 =
                           FStar_Thunk.mkv "Deferring to user tactic"  in
                         giveup_or_defer1
                           (FStar_TypeChecker_Common.TProb problem)
                           uu____22505
                       else solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22510,FStar_Syntax_Syntax.Tm_uvar uu____22511) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22524,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22525;
                    FStar_Syntax_Syntax.pos = uu____22526;
                    FStar_Syntax_Syntax.vars = uu____22527;_},uu____22528))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22565,FStar_Syntax_Syntax.Tm_arrow uu____22566) ->
                  solve_t' env
                    (let uu___3242_22594 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3242_22594.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3242_22594.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3242_22594.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3242_22594.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3242_22594.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3242_22594.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3242_22594.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3242_22594.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3242_22594.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22595;
                    FStar_Syntax_Syntax.pos = uu____22596;
                    FStar_Syntax_Syntax.vars = uu____22597;_},uu____22598),FStar_Syntax_Syntax.Tm_arrow
                 uu____22599) ->
                  solve_t' env
                    (let uu___3242_22651 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3242_22651.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3242_22651.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3242_22651.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3242_22651.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3242_22651.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3242_22651.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3242_22651.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3242_22651.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3242_22651.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22652,FStar_Syntax_Syntax.Tm_uvar uu____22653) ->
                  let uu____22666 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22666
              | (uu____22667,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22668;
                    FStar_Syntax_Syntax.pos = uu____22669;
                    FStar_Syntax_Syntax.vars = uu____22670;_},uu____22671))
                  ->
                  let uu____22708 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22708
              | (FStar_Syntax_Syntax.Tm_uvar uu____22709,uu____22710) ->
                  let uu____22723 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22723
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22724;
                    FStar_Syntax_Syntax.pos = uu____22725;
                    FStar_Syntax_Syntax.vars = uu____22726;_},uu____22727),uu____22728)
                  ->
                  let uu____22765 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22765
              | (FStar_Syntax_Syntax.Tm_refine uu____22766,uu____22767) ->
                  let t21 =
                    let uu____22775 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22775  in
                  solve_t env
                    (let uu___3277_22801 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3277_22801.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3277_22801.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3277_22801.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3277_22801.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3277_22801.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3277_22801.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3277_22801.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3277_22801.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3277_22801.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22802,FStar_Syntax_Syntax.Tm_refine uu____22803) ->
                  let t11 =
                    let uu____22811 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22811  in
                  solve_t env
                    (let uu___3284_22837 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3284_22837.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3284_22837.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3284_22837.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3284_22837.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3284_22837.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3284_22837.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3284_22837.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3284_22837.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3284_22837.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22919 =
                    let uu____22920 = guard_of_prob env wl problem t1 t2  in
                    match uu____22920 with
                    | (guard,wl1) ->
                        let uu____22927 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22927
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23146 = br1  in
                        (match uu____23146 with
                         | (p1,w1,uu____23175) ->
                             let uu____23192 = br2  in
                             (match uu____23192 with
                              | (p2,w2,uu____23215) ->
                                  let uu____23220 =
                                    let uu____23222 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23222  in
                                  if uu____23220
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23249 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23249 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23286 = br2  in
                                         (match uu____23286 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23319 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23319
                                                 in
                                              let uu____23324 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23355,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23376) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23435 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23435 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23324
                                                (fun uu____23507  ->
                                                   match uu____23507 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23544 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23544
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23565
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23565
                                                              then
                                                                let uu____23570
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23572
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23570
                                                                  uu____23572
                                                              else ());
                                                             (let uu____23578
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23578
                                                                (fun
                                                                   uu____23614
                                                                    ->
                                                                   match uu____23614
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
                    | uu____23743 -> FStar_Pervasives_Native.None  in
                  let uu____23784 = solve_branches wl brs1 brs2  in
                  (match uu____23784 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23810 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23810 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23837 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23837 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23871 =
                                FStar_List.map
                                  (fun uu____23883  ->
                                     match uu____23883 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23871  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23892 =
                              let uu____23893 =
                                let uu____23894 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23894
                                  (let uu___3383_23902 = wl3  in
                                   {
                                     attempting =
                                       (uu___3383_23902.attempting);
                                     wl_deferred =
                                       (uu___3383_23902.wl_deferred);
                                     ctr = (uu___3383_23902.ctr);
                                     defer_ok = (uu___3383_23902.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3383_23902.umax_heuristic_ok);
                                     tcenv = (uu___3383_23902.tcenv);
                                     wl_implicits =
                                       (uu___3383_23902.wl_implicits)
                                   })
                                 in
                              solve env uu____23893  in
                            (match uu____23892 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23907 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23916 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23916 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23919,uu____23920) ->
                  let head1 =
                    let uu____23944 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23944
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23990 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23990
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24036 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24036
                    then
                      let uu____24040 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24042 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24044 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24040 uu____24042 uu____24044
                    else ());
                   (let no_free_uvars t =
                      (let uu____24058 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24058) &&
                        (let uu____24062 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24062)
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
                      let uu____24081 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24081 = FStar_Syntax_Util.Equal  in
                    let uu____24082 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24082
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24086 = equal t1 t2  in
                         (if uu____24086
                          then
                            let uu____24089 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24089
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24094 =
                            let uu____24101 = equal t1 t2  in
                            if uu____24101
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24114 = mk_eq2 wl env orig t1 t2  in
                               match uu____24114 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24094 with
                          | (guard,wl1) ->
                              let uu____24135 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24135))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24138,uu____24139) ->
                  let head1 =
                    let uu____24147 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24147
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24193 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24193
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24239 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24239
                    then
                      let uu____24243 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24245 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24247 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24243 uu____24245 uu____24247
                    else ());
                   (let no_free_uvars t =
                      (let uu____24261 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24261) &&
                        (let uu____24265 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24265)
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
                      let uu____24284 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24284 = FStar_Syntax_Util.Equal  in
                    let uu____24285 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24285
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24289 = equal t1 t2  in
                         (if uu____24289
                          then
                            let uu____24292 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24292
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24297 =
                            let uu____24304 = equal t1 t2  in
                            if uu____24304
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24317 = mk_eq2 wl env orig t1 t2  in
                               match uu____24317 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24297 with
                          | (guard,wl1) ->
                              let uu____24338 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24338))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24341,uu____24342) ->
                  let head1 =
                    let uu____24344 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24344
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24390 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24390
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24436 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24436
                    then
                      let uu____24440 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24442 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24444 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24440 uu____24442 uu____24444
                    else ());
                   (let no_free_uvars t =
                      (let uu____24458 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24458) &&
                        (let uu____24462 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24462)
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
                      let uu____24481 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24481 = FStar_Syntax_Util.Equal  in
                    let uu____24482 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24482
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24486 = equal t1 t2  in
                         (if uu____24486
                          then
                            let uu____24489 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24489
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24494 =
                            let uu____24501 = equal t1 t2  in
                            if uu____24501
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24514 = mk_eq2 wl env orig t1 t2  in
                               match uu____24514 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24494 with
                          | (guard,wl1) ->
                              let uu____24535 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24535))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24538,uu____24539) ->
                  let head1 =
                    let uu____24541 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24541
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24587 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24587
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24633 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24633
                    then
                      let uu____24637 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24639 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24641 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24637 uu____24639 uu____24641
                    else ());
                   (let no_free_uvars t =
                      (let uu____24655 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24655) &&
                        (let uu____24659 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24659)
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
                      let uu____24678 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24678 = FStar_Syntax_Util.Equal  in
                    let uu____24679 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24679
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24683 = equal t1 t2  in
                         (if uu____24683
                          then
                            let uu____24686 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24686
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24691 =
                            let uu____24698 = equal t1 t2  in
                            if uu____24698
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24711 = mk_eq2 wl env orig t1 t2  in
                               match uu____24711 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24691 with
                          | (guard,wl1) ->
                              let uu____24732 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24732))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24735,uu____24736) ->
                  let head1 =
                    let uu____24738 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24738
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24784 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24784
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24830 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24830
                    then
                      let uu____24834 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24836 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24838 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24834 uu____24836 uu____24838
                    else ());
                   (let no_free_uvars t =
                      (let uu____24852 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24852) &&
                        (let uu____24856 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24856)
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
                      let uu____24875 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24875 = FStar_Syntax_Util.Equal  in
                    let uu____24876 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24876
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24880 = equal t1 t2  in
                         (if uu____24880
                          then
                            let uu____24883 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24883
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24888 =
                            let uu____24895 = equal t1 t2  in
                            if uu____24895
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24908 = mk_eq2 wl env orig t1 t2  in
                               match uu____24908 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24888 with
                          | (guard,wl1) ->
                              let uu____24929 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24929))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24932,uu____24933) ->
                  let head1 =
                    let uu____24951 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24951
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24997 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24997
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25043 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25043
                    then
                      let uu____25047 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25049 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25051 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25047 uu____25049 uu____25051
                    else ());
                   (let no_free_uvars t =
                      (let uu____25065 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25065) &&
                        (let uu____25069 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25069)
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
                      let uu____25088 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25088 = FStar_Syntax_Util.Equal  in
                    let uu____25089 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25089
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25093 = equal t1 t2  in
                         (if uu____25093
                          then
                            let uu____25096 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25096
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25101 =
                            let uu____25108 = equal t1 t2  in
                            if uu____25108
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25121 = mk_eq2 wl env orig t1 t2  in
                               match uu____25121 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25101 with
                          | (guard,wl1) ->
                              let uu____25142 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25142))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25145,FStar_Syntax_Syntax.Tm_match uu____25146) ->
                  let head1 =
                    let uu____25170 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25170
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25216 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25216
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25262 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25262
                    then
                      let uu____25266 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25268 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25270 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25266 uu____25268 uu____25270
                    else ());
                   (let no_free_uvars t =
                      (let uu____25284 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25284) &&
                        (let uu____25288 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25288)
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
                      let uu____25307 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25307 = FStar_Syntax_Util.Equal  in
                    let uu____25308 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25308
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25312 = equal t1 t2  in
                         (if uu____25312
                          then
                            let uu____25315 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25315
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25320 =
                            let uu____25327 = equal t1 t2  in
                            if uu____25327
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25340 = mk_eq2 wl env orig t1 t2  in
                               match uu____25340 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25320 with
                          | (guard,wl1) ->
                              let uu____25361 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25361))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25364,FStar_Syntax_Syntax.Tm_uinst uu____25365) ->
                  let head1 =
                    let uu____25373 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25373
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25419 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25419
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25465 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25465
                    then
                      let uu____25469 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25471 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25473 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25469 uu____25471 uu____25473
                    else ());
                   (let no_free_uvars t =
                      (let uu____25487 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25487) &&
                        (let uu____25491 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25491)
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
                      let uu____25510 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25510 = FStar_Syntax_Util.Equal  in
                    let uu____25511 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25511
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25515 = equal t1 t2  in
                         (if uu____25515
                          then
                            let uu____25518 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25518
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25523 =
                            let uu____25530 = equal t1 t2  in
                            if uu____25530
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25543 = mk_eq2 wl env orig t1 t2  in
                               match uu____25543 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25523 with
                          | (guard,wl1) ->
                              let uu____25564 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25564))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25567,FStar_Syntax_Syntax.Tm_name uu____25568) ->
                  let head1 =
                    let uu____25570 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25570
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25616 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25616
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25662 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25662
                    then
                      let uu____25666 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25668 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25670 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25666 uu____25668 uu____25670
                    else ());
                   (let no_free_uvars t =
                      (let uu____25684 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25684) &&
                        (let uu____25688 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25688)
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
                      let uu____25707 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25707 = FStar_Syntax_Util.Equal  in
                    let uu____25708 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25708
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25712 = equal t1 t2  in
                         (if uu____25712
                          then
                            let uu____25715 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25715
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25720 =
                            let uu____25727 = equal t1 t2  in
                            if uu____25727
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25740 = mk_eq2 wl env orig t1 t2  in
                               match uu____25740 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25720 with
                          | (guard,wl1) ->
                              let uu____25761 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25761))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25764,FStar_Syntax_Syntax.Tm_constant uu____25765) ->
                  let head1 =
                    let uu____25767 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25767
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25807 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25807
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25847 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25847
                    then
                      let uu____25851 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25853 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25855 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25851 uu____25853 uu____25855
                    else ());
                   (let no_free_uvars t =
                      (let uu____25869 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25869) &&
                        (let uu____25873 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25873)
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
                      let uu____25892 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25892 = FStar_Syntax_Util.Equal  in
                    let uu____25893 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25893
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25897 = equal t1 t2  in
                         (if uu____25897
                          then
                            let uu____25900 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25900
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25905 =
                            let uu____25912 = equal t1 t2  in
                            if uu____25912
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25925 = mk_eq2 wl env orig t1 t2  in
                               match uu____25925 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25905 with
                          | (guard,wl1) ->
                              let uu____25946 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25946))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25949,FStar_Syntax_Syntax.Tm_fvar uu____25950) ->
                  let head1 =
                    let uu____25952 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25952
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25998 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25998
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26044 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26044
                    then
                      let uu____26048 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26050 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26052 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26048 uu____26050 uu____26052
                    else ());
                   (let no_free_uvars t =
                      (let uu____26066 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26066) &&
                        (let uu____26070 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26070)
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
                      let uu____26089 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26089 = FStar_Syntax_Util.Equal  in
                    let uu____26090 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26090
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26094 = equal t1 t2  in
                         (if uu____26094
                          then
                            let uu____26097 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26097
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26102 =
                            let uu____26109 = equal t1 t2  in
                            if uu____26109
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26122 = mk_eq2 wl env orig t1 t2  in
                               match uu____26122 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26102 with
                          | (guard,wl1) ->
                              let uu____26143 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26143))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26146,FStar_Syntax_Syntax.Tm_app uu____26147) ->
                  let head1 =
                    let uu____26165 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26165
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26205 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26205
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26245 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26245
                    then
                      let uu____26249 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26251 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26253 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26249 uu____26251 uu____26253
                    else ());
                   (let no_free_uvars t =
                      (let uu____26267 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26267) &&
                        (let uu____26271 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26271)
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
                      let uu____26290 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26290 = FStar_Syntax_Util.Equal  in
                    let uu____26291 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26291
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26295 = equal t1 t2  in
                         (if uu____26295
                          then
                            let uu____26298 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26298
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26303 =
                            let uu____26310 = equal t1 t2  in
                            if uu____26310
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26323 = mk_eq2 wl env orig t1 t2  in
                               match uu____26323 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26303 with
                          | (guard,wl1) ->
                              let uu____26344 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26344))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26347,FStar_Syntax_Syntax.Tm_let uu____26348) ->
                  let uu____26375 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26375
                  then
                    let uu____26378 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26378
                  else
                    (let uu____26381 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26381 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26384,uu____26385) ->
                  let uu____26399 =
                    let uu____26405 =
                      let uu____26407 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26409 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26411 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26413 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26407 uu____26409 uu____26411 uu____26413
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26405)
                     in
                  FStar_Errors.raise_error uu____26399
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26417,FStar_Syntax_Syntax.Tm_let uu____26418) ->
                  let uu____26432 =
                    let uu____26438 =
                      let uu____26440 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26442 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26444 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26446 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26440 uu____26442 uu____26444 uu____26446
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26438)
                     in
                  FStar_Errors.raise_error uu____26432
                    t1.FStar_Syntax_Syntax.pos
              | uu____26450 ->
                  let uu____26455 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26455 orig))))

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
          (let uu____26521 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26521
           then
             let uu____26526 =
               let uu____26528 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26528  in
             let uu____26529 =
               let uu____26531 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26531  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26526 uu____26529
           else ());
          (let uu____26535 =
             let uu____26537 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26537  in
           if uu____26535
           then
             let uu____26540 =
               FStar_Thunk.mk
                 (fun uu____26545  ->
                    let uu____26546 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26548 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26546 uu____26548)
                in
             giveup env uu____26540 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26570 =
                  FStar_Thunk.mk
                    (fun uu____26575  ->
                       let uu____26576 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26578 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26576 uu____26578)
                   in
                giveup env uu____26570 orig)
             else
               (let uu____26583 =
                  FStar_List.fold_left2
                    (fun uu____26604  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26604 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26625 =
                                 let uu____26630 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26631 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26630
                                   FStar_TypeChecker_Common.EQ uu____26631
                                   "effect universes"
                                  in
                               (match uu____26625 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26583 with
                | (univ_sub_probs,wl1) ->
                    let uu____26651 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26651 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26659 =
                           FStar_List.fold_right2
                             (fun uu____26696  ->
                                fun uu____26697  ->
                                  fun uu____26698  ->
                                    match (uu____26696, uu____26697,
                                            uu____26698)
                                    with
                                    | ((a1,uu____26742),(a2,uu____26744),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26777 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26777 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26659 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26804 =
                                  let uu____26807 =
                                    let uu____26810 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26810
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26807
                                   in
                                FStar_List.append univ_sub_probs uu____26804
                                 in
                              let guard =
                                let guard =
                                  let uu____26832 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26832  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3535_26841 = wl3  in
                                {
                                  attempting = (uu___3535_26841.attempting);
                                  wl_deferred = (uu___3535_26841.wl_deferred);
                                  ctr = (uu___3535_26841.ctr);
                                  defer_ok = (uu___3535_26841.defer_ok);
                                  smt_ok = (uu___3535_26841.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3535_26841.umax_heuristic_ok);
                                  tcenv = (uu___3535_26841.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26843 = attempt sub_probs wl5  in
                              solve env uu____26843))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26861 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26861
           then
             let uu____26866 =
               let uu____26868 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26868
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26870 =
               let uu____26872 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26872
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26866 uu____26870
           else ());
          (let uu____26877 =
             let uu____26882 =
               let uu____26887 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26887
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26882
               (fun uu____26904  ->
                  match uu____26904 with
                  | (c,g) ->
                      let uu____26915 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26915, g))
              in
           match uu____26877 with
           | (c12,g_lift) ->
               ((let uu____26919 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26919
                 then
                   let uu____26924 =
                     let uu____26926 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26926
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26928 =
                     let uu____26930 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26930
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26924 uu____26928
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3555_26940 = wl  in
                     {
                       attempting = (uu___3555_26940.attempting);
                       wl_deferred = (uu___3555_26940.wl_deferred);
                       ctr = (uu___3555_26940.ctr);
                       defer_ok = (uu___3555_26940.defer_ok);
                       smt_ok = (uu___3555_26940.smt_ok);
                       umax_heuristic_ok =
                         (uu___3555_26940.umax_heuristic_ok);
                       tcenv = (uu___3555_26940.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26941 =
                     let rec is_uvar1 t =
                       let uu____26955 =
                         let uu____26956 = FStar_Syntax_Subst.compress t  in
                         uu____26956.FStar_Syntax_Syntax.n  in
                       match uu____26955 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26960 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26975) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26981) ->
                           is_uvar1 t1
                       | uu____27006 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27040  ->
                          fun uu____27041  ->
                            fun uu____27042  ->
                              match (uu____27040, uu____27041, uu____27042)
                              with
                              | ((a1,uu____27086),(a2,uu____27088),(is_sub_probs,wl2))
                                  ->
                                  let uu____27121 = is_uvar1 a1  in
                                  if uu____27121
                                  then
                                    ((let uu____27131 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27131
                                      then
                                        let uu____27136 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27138 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27136 uu____27138
                                      else ());
                                     (let uu____27143 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27143 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26941 with
                   | (is_sub_probs,wl2) ->
                       let uu____27171 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27171 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27179 =
                              let uu____27184 =
                                let uu____27185 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27185
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27184
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27179 with
                             | (uu____27192,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27203 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27205 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27203 s uu____27205
                                    in
                                 let uu____27208 =
                                   let uu____27237 =
                                     let uu____27238 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27238.FStar_Syntax_Syntax.n  in
                                   match uu____27237 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27298 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27298 with
                                        | (a::bs1,c3) ->
                                            let uu____27354 =
                                              let uu____27373 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27373
                                                (fun uu____27477  ->
                                                   match uu____27477 with
                                                   | (l1,l2) ->
                                                       let uu____27550 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27550))
                                               in
                                            (match uu____27354 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27655 ->
                                       let uu____27656 =
                                         let uu____27662 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27662)
                                          in
                                       FStar_Errors.raise_error uu____27656 r
                                    in
                                 (match uu____27208 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27738 =
                                        let uu____27745 =
                                          let uu____27746 =
                                            let uu____27747 =
                                              let uu____27754 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27754,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27747
                                             in
                                          [uu____27746]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27745
                                          (fun b  ->
                                             let uu____27770 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27772 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27774 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27770 uu____27772
                                               uu____27774) r
                                         in
                                      (match uu____27738 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27784 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27784
                                             then
                                               let uu____27789 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27798 =
                                                          let uu____27800 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27800
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27798) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27789
                                             else ());
                                            (let wl4 =
                                               let uu___3627_27808 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3627_27808.attempting);
                                                 wl_deferred =
                                                   (uu___3627_27808.wl_deferred);
                                                 ctr = (uu___3627_27808.ctr);
                                                 defer_ok =
                                                   (uu___3627_27808.defer_ok);
                                                 smt_ok =
                                                   (uu___3627_27808.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3627_27808.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3627_27808.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27833 =
                                                        let uu____27840 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27840, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27833) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27857 =
                                               let f_sort_is =
                                                 let uu____27867 =
                                                   let uu____27868 =
                                                     let uu____27871 =
                                                       let uu____27872 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27872.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27871
                                                      in
                                                   uu____27868.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27867 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27883,uu____27884::is)
                                                     ->
                                                     let uu____27926 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27926
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27959 ->
                                                     let uu____27960 =
                                                       let uu____27966 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27966)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27960 r
                                                  in
                                               let uu____27972 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28007  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28007
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28028 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28028
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27972
                                                in
                                             match uu____27857 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28053 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28053
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28054 =
                                                   let g_sort_is =
                                                     let uu____28064 =
                                                       let uu____28065 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28065.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28064 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28070,uu____28071::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28131 ->
                                                         let uu____28132 =
                                                           let uu____28138 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28138)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28132 r
                                                      in
                                                   let uu____28144 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28179  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28179
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28200
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28200
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28144
                                                    in
                                                 (match uu____28054 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28227 =
                                                          let uu____28232 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28233 =
                                                            let uu____28234 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28234
                                                             in
                                                          (uu____28232,
                                                            uu____28233)
                                                           in
                                                        match uu____28227
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28262 =
                                                          let uu____28265 =
                                                            let uu____28268 =
                                                              let uu____28271
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28271
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28268
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28265
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28262
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28295 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28295
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
                                                        let uu____28306 =
                                                          let uu____28309 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28312  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28312)
                                                            uu____28309
                                                           in
                                                        solve_prob orig
                                                          uu____28306 [] wl6
                                                         in
                                                      let uu____28313 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28313))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28336 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28338 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28338]
              | x -> x  in
            let c12 =
              let uu___3693_28341 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3693_28341.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3693_28341.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3693_28341.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3693_28341.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28342 =
              let uu____28347 =
                FStar_All.pipe_right
                  (let uu___3696_28349 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3696_28349.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3696_28349.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3696_28349.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3696_28349.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28347
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28342
              (fun uu____28363  ->
                 match uu____28363 with
                 | (c,g) ->
                     let uu____28370 =
                       let uu____28372 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28372  in
                     if uu____28370
                     then
                       let uu____28375 =
                         let uu____28381 =
                           let uu____28383 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28385 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28383 uu____28385
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28381)
                          in
                       FStar_Errors.raise_error uu____28375 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28391 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28391
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28397 = lift_c1 ()  in
               solve_eq uu____28397 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28406  ->
                         match uu___31_28406 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28411 -> false))
                  in
               let uu____28413 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28443)::uu____28444,(wp2,uu____28446)::uu____28447)
                     -> (wp1, wp2)
                 | uu____28520 ->
                     let uu____28545 =
                       let uu____28551 =
                         let uu____28553 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28555 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28553 uu____28555
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28551)
                        in
                     FStar_Errors.raise_error uu____28545
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28413 with
               | (wpc1,wpc2) ->
                   let uu____28565 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28565
                   then
                     let uu____28568 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28568 wl
                   else
                     (let uu____28572 =
                        let uu____28579 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28579  in
                      match uu____28572 with
                      | (c2_decl,qualifiers) ->
                          let uu____28600 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28600
                          then
                            let c1_repr =
                              let uu____28607 =
                                let uu____28608 =
                                  let uu____28609 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28609  in
                                let uu____28610 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28608 uu____28610
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28607
                               in
                            let c2_repr =
                              let uu____28613 =
                                let uu____28614 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28615 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28614 uu____28615
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28613
                               in
                            let uu____28617 =
                              let uu____28622 =
                                let uu____28624 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28626 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28624
                                  uu____28626
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28622
                               in
                            (match uu____28617 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28632 = attempt [prob] wl2  in
                                 solve env uu____28632)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28652 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28652
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28675 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28675
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
                                        let uu____28685 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28685 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28692 =
                                        let uu____28699 =
                                          let uu____28700 =
                                            let uu____28717 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28720 =
                                              let uu____28731 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28731; wpc1_2]  in
                                            (uu____28717, uu____28720)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28700
                                           in
                                        FStar_Syntax_Syntax.mk uu____28699
                                         in
                                      uu____28692
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
                                     let uu____28780 =
                                       let uu____28787 =
                                         let uu____28788 =
                                           let uu____28805 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28808 =
                                             let uu____28819 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28828 =
                                               let uu____28839 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28839; wpc1_2]  in
                                             uu____28819 :: uu____28828  in
                                           (uu____28805, uu____28808)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28788
                                          in
                                       FStar_Syntax_Syntax.mk uu____28787  in
                                     uu____28780 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28893 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28893
                              then
                                let uu____28898 =
                                  let uu____28900 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28900
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28898
                              else ());
                             (let uu____28904 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28904 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28913 =
                                      let uu____28916 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28919  ->
                                           FStar_Pervasives_Native.Some
                                             _28919) uu____28916
                                       in
                                    solve_prob orig uu____28913 [] wl1  in
                                  let uu____28920 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28920))))
           in
        let uu____28921 = FStar_Util.physical_equality c1 c2  in
        if uu____28921
        then
          let uu____28924 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28924
        else
          ((let uu____28928 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28928
            then
              let uu____28933 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28935 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28933
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28935
            else ());
           (let uu____28940 =
              let uu____28949 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28952 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28949, uu____28952)  in
            match uu____28940 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28970),FStar_Syntax_Syntax.Total
                    (t2,uu____28972)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28989 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28989 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28991,FStar_Syntax_Syntax.Total uu____28992) ->
                     let uu____29009 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29009 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29013),FStar_Syntax_Syntax.Total
                    (t2,uu____29015)) ->
                     let uu____29032 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29032 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29035),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29037)) ->
                     let uu____29054 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29054 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29057),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29059)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29076 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29076 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29079),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29081)) ->
                     let uu____29098 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29098 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29101,FStar_Syntax_Syntax.Comp uu____29102) ->
                     let uu____29111 =
                       let uu___3820_29114 = problem  in
                       let uu____29117 =
                         let uu____29118 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29118
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3820_29114.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29117;
                         FStar_TypeChecker_Common.relation =
                           (uu___3820_29114.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3820_29114.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3820_29114.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3820_29114.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3820_29114.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3820_29114.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3820_29114.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3820_29114.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29111 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29119,FStar_Syntax_Syntax.Comp uu____29120) ->
                     let uu____29129 =
                       let uu___3820_29132 = problem  in
                       let uu____29135 =
                         let uu____29136 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29136
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3820_29132.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29135;
                         FStar_TypeChecker_Common.relation =
                           (uu___3820_29132.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3820_29132.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3820_29132.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3820_29132.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3820_29132.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3820_29132.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3820_29132.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3820_29132.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29129 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29137,FStar_Syntax_Syntax.GTotal uu____29138) ->
                     let uu____29147 =
                       let uu___3832_29150 = problem  in
                       let uu____29153 =
                         let uu____29154 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29154
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3832_29150.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3832_29150.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3832_29150.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29153;
                         FStar_TypeChecker_Common.element =
                           (uu___3832_29150.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3832_29150.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3832_29150.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3832_29150.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3832_29150.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3832_29150.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29147 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29155,FStar_Syntax_Syntax.Total uu____29156) ->
                     let uu____29165 =
                       let uu___3832_29168 = problem  in
                       let uu____29171 =
                         let uu____29172 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29172
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3832_29168.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3832_29168.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3832_29168.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29171;
                         FStar_TypeChecker_Common.element =
                           (uu___3832_29168.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3832_29168.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3832_29168.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3832_29168.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3832_29168.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3832_29168.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29165 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29173,FStar_Syntax_Syntax.Comp uu____29174) ->
                     let uu____29175 =
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
                     if uu____29175
                     then
                       let uu____29178 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29178 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29185 =
                            let uu____29190 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29190
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29199 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29200 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29199, uu____29200))
                             in
                          match uu____29185 with
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
                           (let uu____29208 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29208
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29216 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29216 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29219 =
                                  FStar_Thunk.mk
                                    (fun uu____29224  ->
                                       let uu____29225 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29227 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29225 uu____29227)
                                   in
                                giveup env uu____29219 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29238 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29238 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29288 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29288 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29313 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29344  ->
                match uu____29344 with
                | (u1,u2) ->
                    let uu____29352 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29354 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29352 uu____29354))
         in
      FStar_All.pipe_right uu____29313 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29391,[])) when
          let uu____29418 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29418 -> "{}"
      | uu____29421 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29448 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29448
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29460 =
              FStar_List.map
                (fun uu____29473  ->
                   match uu____29473 with
                   | (uu____29480,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29460 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29491 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29491 imps
  
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
                  let uu____29548 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29548
                  then
                    let uu____29556 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29558 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29556
                      (rel_to_string rel) uu____29558
                  else "TOP"  in
                let uu____29564 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29564 with
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
              let uu____29624 =
                let uu____29627 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29630  -> FStar_Pervasives_Native.Some _29630)
                  uu____29627
                 in
              FStar_Syntax_Syntax.new_bv uu____29624 t1  in
            let uu____29631 =
              let uu____29636 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29636
               in
            match uu____29631 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29694 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29694
         then
           let uu____29699 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29699
         else ());
        (let uu____29706 =
           FStar_Util.record_time (fun uu____29713  -> solve env probs)  in
         match uu____29706 with
         | (sol,ms) ->
             ((let uu____29725 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29725
               then
                 let uu____29730 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29730
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29743 =
                     FStar_Util.record_time
                       (fun uu____29750  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29743 with
                    | ((),ms1) ->
                        ((let uu____29761 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29761
                          then
                            let uu____29766 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29766
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29778 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29778
                     then
                       let uu____29785 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29785
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
          ((let uu____29811 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29811
            then
              let uu____29816 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29816
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29824 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29824
             then
               let uu____29829 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29829
             else ());
            (let f2 =
               let uu____29835 =
                 let uu____29836 = FStar_Syntax_Util.unmeta f1  in
                 uu____29836.FStar_Syntax_Syntax.n  in
               match uu____29835 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29840 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3949_29841 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3949_29841.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3949_29841.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3949_29841.FStar_TypeChecker_Common.implicits)
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
            let uu____29884 =
              let uu____29885 =
                let uu____29886 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29887  ->
                       FStar_TypeChecker_Common.NonTrivial _29887)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29886;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29885  in
            FStar_All.pipe_left
              (fun _29894  -> FStar_Pervasives_Native.Some _29894)
              uu____29884
  
let with_guard_no_simp :
  'Auu____29904 .
    'Auu____29904 ->
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
            let uu____29944 =
              let uu____29945 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29946  -> FStar_TypeChecker_Common.NonTrivial _29946)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29945;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29944
  
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
          (let uu____29979 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29979
           then
             let uu____29984 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29986 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29984
               uu____29986
           else ());
          (let uu____29991 =
             let uu____29996 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29996
              in
           match uu____29991 with
           | (prob,wl) ->
               let g =
                 let uu____30004 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30012  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30004  in
               ((let uu____30030 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30030
                 then
                   let uu____30035 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30035
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
        let uu____30056 = try_teq true env t1 t2  in
        match uu____30056 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30061 = FStar_TypeChecker_Env.get_range env  in
              let uu____30062 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30061 uu____30062);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30070 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30070
              then
                let uu____30075 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30077 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30079 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30075
                  uu____30077 uu____30079
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
        (let uu____30103 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30103
         then
           let uu____30108 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30110 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30108
             uu____30110
         else ());
        (let uu____30115 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30115 with
         | (prob,x,wl) ->
             let g =
               let uu____30130 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30139  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30130  in
             ((let uu____30157 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30157
               then
                 let uu____30162 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30162
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30170 =
                     let uu____30171 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30171 g1  in
                   FStar_Pervasives_Native.Some uu____30170)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30193 = FStar_TypeChecker_Env.get_range env  in
          let uu____30194 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30193 uu____30194
  
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
        (let uu____30223 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30223
         then
           let uu____30228 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30230 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30228 uu____30230
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30241 =
           let uu____30248 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30248 "sub_comp"
            in
         match uu____30241 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30261 =
                 FStar_Util.record_time
                   (fun uu____30273  ->
                      let uu____30274 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30283  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30274)
                  in
               match uu____30261 with
               | (r,ms) ->
                   ((let uu____30311 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30311
                     then
                       let uu____30316 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30318 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30320 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30316 uu____30318
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30320
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
      fun uu____30358  ->
        match uu____30358 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30401 =
                 let uu____30407 =
                   let uu____30409 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30411 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30409 uu____30411
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30407)  in
               let uu____30415 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30401 uu____30415)
               in
            let equiv1 v1 v' =
              let uu____30428 =
                let uu____30433 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30434 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30433, uu____30434)  in
              match uu____30428 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30454 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30485 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30485 with
                      | FStar_Syntax_Syntax.U_unif uu____30492 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30521  ->
                                    match uu____30521 with
                                    | (u,v') ->
                                        let uu____30530 = equiv1 v1 v'  in
                                        if uu____30530
                                        then
                                          let uu____30535 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30535 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30556 -> []))
               in
            let uu____30561 =
              let wl =
                let uu___4060_30565 = empty_worklist env  in
                {
                  attempting = (uu___4060_30565.attempting);
                  wl_deferred = (uu___4060_30565.wl_deferred);
                  ctr = (uu___4060_30565.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4060_30565.smt_ok);
                  umax_heuristic_ok = (uu___4060_30565.umax_heuristic_ok);
                  tcenv = (uu___4060_30565.tcenv);
                  wl_implicits = (uu___4060_30565.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30584  ->
                      match uu____30584 with
                      | (lb,v1) ->
                          let uu____30591 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30591 with
                           | USolved wl1 -> ()
                           | uu____30594 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30605 =
              match uu____30605 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30617) -> true
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
                      uu____30641,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30643,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30654) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30662,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30671 -> false)
               in
            let uu____30677 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30694  ->
                      match uu____30694 with
                      | (u,v1) ->
                          let uu____30702 = check_ineq (u, v1)  in
                          if uu____30702
                          then true
                          else
                            ((let uu____30710 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30710
                              then
                                let uu____30715 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30717 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30715
                                  uu____30717
                              else ());
                             false)))
               in
            if uu____30677
            then ()
            else
              ((let uu____30727 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30727
                then
                  ((let uu____30733 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30733);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30745 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30745))
                else ());
               (let uu____30758 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30758))
  
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
        let fail1 uu____30831 =
          match uu____30831 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4137_30854 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4137_30854.attempting);
            wl_deferred = (uu___4137_30854.wl_deferred);
            ctr = (uu___4137_30854.ctr);
            defer_ok;
            smt_ok = (uu___4137_30854.smt_ok);
            umax_heuristic_ok = (uu___4137_30854.umax_heuristic_ok);
            tcenv = (uu___4137_30854.tcenv);
            wl_implicits = (uu___4137_30854.wl_implicits)
          }  in
        (let uu____30857 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30857
         then
           let uu____30862 = FStar_Util.string_of_bool defer_ok  in
           let uu____30864 = wl_to_string wl  in
           let uu____30866 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30862 uu____30864 uu____30866
         else ());
        (let g1 =
           let uu____30872 = solve_and_commit env wl fail1  in
           match uu____30872 with
           | FStar_Pervasives_Native.Some
               (uu____30879::uu____30880,uu____30881) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4152_30910 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4152_30910.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4152_30910.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30911 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4157_30920 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4157_30920.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4157_30920.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4157_30920.FStar_TypeChecker_Common.implicits)
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
          (let uu____30996 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____30996
           then
             let uu____31001 = guard_to_string env g  in
             let uu____31003 = FStar_Util.stack_dump ()  in
             FStar_Util.print2
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\nbacktrace=%s\n"
               uu____31001 uu____31003
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4171_31010 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred =
                 (uu___4171_31010.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4171_31010.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4171_31010.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31011 =
             let uu____31013 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31013  in
           if uu____31011
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____31025 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31026 =
                        let uu____31028 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31028
                         in
                      FStar_Errors.diag uu____31025 uu____31026)
                   else ();
                   (let vc1 =
                      let uu____31034 =
                        let uu____31038 =
                          let uu____31040 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31040  in
                        FStar_Pervasives_Native.Some uu____31038  in
                      FStar_Profiling.profile
                        (fun uu____31043  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31034 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____31047 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31048 =
                         let uu____31050 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31050
                          in
                       FStar_Errors.diag uu____31047 uu____31048)
                    else ();
                    (let uu____31056 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31056 "discharge_guard'" env vc1);
                    (let uu____31058 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31058 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____31067 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31068 =
                                 let uu____31070 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31070
                                  in
                               FStar_Errors.diag uu____31067 uu____31068)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31080 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31081 =
                                 let uu____31083 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31083
                                  in
                               FStar_Errors.diag uu____31080 uu____31081)
                            else ();
                            (let vcs =
                               let uu____31097 = FStar_Options.use_tactics ()
                                  in
                               if uu____31097
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31119  ->
                                      (let uu____31121 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31121);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31165  ->
                                               match uu____31165 with
                                               | (env1,goal,opts) ->
                                                   let uu____31181 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31181, opts)))))
                               else
                                 (let uu____31185 =
                                    let uu____31192 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31192)  in
                                  [uu____31185])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31225  ->
                                     match uu____31225 with
                                     | (env1,goal,opts) ->
                                         let uu____31235 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31235 with
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
                                                 (let uu____31246 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31247 =
                                                    let uu____31249 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31251 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31249 uu____31251
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31246 uu____31247)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31258 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31259 =
                                                    let uu____31261 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31261
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31258 uu____31259)
                                               else ();
                                               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                 use_env_range_msg env1 goal1;
                                               FStar_Options.pop ())))));
                            FStar_Pervasives_Native.Some ret_g))))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31279 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31279 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31288 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31288
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31302 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31302 with
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
        let uu____31332 = try_teq false env t1 t2  in
        match uu____31332 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (teq_maybe_defer :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let should_defer =
          let uu____31362 =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          match uu____31362 with | [] -> false | uu____31367 -> true  in
        if should_defer
        then
          let uu____31372 =
            let uu____31377 = FStar_TypeChecker_Env.get_range env  in
            new_t_problem (empty_worklist env) env t1
              FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
              uu____31377
             in
          match uu____31372 with
          | (prob,wl) ->
              let wl1 =
                let uu____31381 =
                  FStar_Thunk.mkv
                    "deferring for user-provided resolve_implicits hook"
                   in
                defer uu____31381 prob wl  in
              let g =
                let uu____31387 =
                  solve_and_commit env wl1
                    (fun uu____31395  -> FStar_Pervasives_Native.None)
                   in
                FStar_All.pipe_left (with_guard env prob) uu____31387  in
              let g1 = FStar_Option.get g  in
              ((let uu____31414 =
                  FStar_TypeChecker_Env.debug env
                    (FStar_Options.Other "ResolveImplicitsHook")
                   in
                if uu____31414
                then
                  let uu____31418 =
                    let uu____31420 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Range.string_of_range uu____31420  in
                  let uu____31421 = guard_to_string env g1  in
                  FStar_Util.print2 "(%s): Deferred unification: %s\n"
                    uu____31418 uu____31421
                else ());
               g1)
        else teq env t1 t2
  
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
            let uu____31460 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31460 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31467 ->
                     let uu____31468 =
                       let uu____31469 = FStar_Syntax_Subst.compress r  in
                       uu____31469.FStar_Syntax_Syntax.n  in
                     (match uu____31468 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31474) ->
                          unresolved ctx_u'
                      | uu____31491 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31515 = acc  in
            match uu____31515 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31534 = hd1  in
                     (match uu____31534 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31545 = unresolved ctx_u  in
                             if uu____31545
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31556 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31556
                                     then
                                       let uu____31560 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31560
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31569 = teq_nosmt env1 t tm
                                          in
                                       match uu____31569 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4300_31579 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4300_31579.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4300_31579.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4300_31579.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4300_31579.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4300_31579.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4300_31579.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4300_31579.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4303_31581 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4303_31581.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4303_31581.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4303_31581.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                               | uu____31584 ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4308_31596 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4308_31596.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4308_31596.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4308_31596.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4308_31596.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4308_31596.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4308_31596.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4308_31596.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4308_31596.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4308_31596.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4308_31596.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4308_31596.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4308_31596.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4308_31596.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4308_31596.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4308_31596.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4308_31596.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4308_31596.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4308_31596.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4308_31596.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4308_31596.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4308_31596.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4308_31596.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4308_31596.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4308_31596.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4308_31596.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4308_31596.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4308_31596.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4308_31596.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4308_31596.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4308_31596.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4308_31596.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4308_31596.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4308_31596.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4308_31596.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4308_31596.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4308_31596.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4308_31596.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4308_31596.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4308_31596.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4308_31596.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4308_31596.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4308_31596.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4308_31596.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4308_31596.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4308_31596.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4308_31596.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4313_31601 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4313_31601.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4313_31601.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4313_31601.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4313_31601.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4313_31601.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4313_31601.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4313_31601.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4313_31601.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4313_31601.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4313_31601.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4313_31601.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4313_31601.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4313_31601.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4313_31601.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4313_31601.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4313_31601.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4313_31601.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4313_31601.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4313_31601.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4313_31601.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4313_31601.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4313_31601.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4313_31601.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4313_31601.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4313_31601.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4313_31601.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4313_31601.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4313_31601.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4313_31601.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4313_31601.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4313_31601.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4313_31601.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4313_31601.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4313_31601.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4313_31601.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4313_31601.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4313_31601.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31606 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31606
                                   then
                                     let uu____31611 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31613 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31615 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31617 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31611 uu____31613 uu____31615
                                       reason uu____31617
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4319_31624  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31631 =
                                             let uu____31641 =
                                               let uu____31649 =
                                                 let uu____31651 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31653 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31655 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31651 uu____31653
                                                   uu____31655
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31649, r)
                                                in
                                             [uu____31641]  in
                                           FStar_Errors.add_errors
                                             uu____31631);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31674 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31685  ->
                                               let uu____31686 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31688 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31690 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31686 uu____31688
                                                 reason uu____31690)) env2 g1
                                         true
                                        in
                                     match uu____31674 with
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
          let uu___4331_31698 = g  in
          let uu____31699 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4331_31698.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4331_31698.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4331_31698.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31699
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____31714 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____31714
       then
         let uu____31719 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____31719
       else ());
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
      (let uu____31750 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____31750
       then
         let uu____31755 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____31755
       else ());
      (let g1 =
         let uu____31761 = solve_deferred_constraints env g  in
         FStar_All.pipe_right uu____31761 (resolve_implicits env)  in
       match g1.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____31762 = discharge_guard env g1  in
           FStar_All.pipe_left (fun a2  -> ()) uu____31762
       | imp::uu____31764 ->
           let uu____31767 =
             FStar_TypeChecker_Env.lookup_attr env
               FStar_Parser_Const.resolve_implicits_attr_string
              in
           (match uu____31767 with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  (uu____31770,lid::[]);
                FStar_Syntax_Syntax.sigrng = uu____31772;
                FStar_Syntax_Syntax.sigquals = uu____31773;
                FStar_Syntax_Syntax.sigmeta = uu____31774;
                FStar_Syntax_Syntax.sigattrs = uu____31775;
                FStar_Syntax_Syntax.sigopts = uu____31776;_}::uu____31777 ->
                let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv lid
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero) FStar_Pervasives_Native.None
                   in
                let dd =
                  let uu____31792 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                  match uu____31792 with
                  | FStar_Pervasives_Native.Some dd -> dd
                  | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                   in
                let term =
                  let uu____31798 =
                    FStar_Syntax_Syntax.lid_as_fv lid dd
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.fv_to_tm uu____31798  in
                (env.FStar_TypeChecker_Env.try_solve_implicits_hook env term
                   g1.FStar_TypeChecker_Common.implicits;
                 (let uu____31800 = discharge_guard env g1  in
                  FStar_All.pipe_left (fun a3  -> ()) uu____31800))
            | uu____31801 ->
                let uu____31804 =
                  let uu____31810 =
                    let uu____31812 =
                      FStar_Syntax_Print.uvar_to_string
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                       in
                    let uu____31814 =
                      FStar_TypeChecker_Normalize.term_to_string env
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                       in
                    FStar_Util.format3
                      "Failed to resolve implicit argument %s of type %s introduced for %s"
                      uu____31812 uu____31814
                      imp.FStar_TypeChecker_Common.imp_reason
                     in
                  (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                    uu____31810)
                   in
                FStar_Errors.raise_error uu____31804
                  imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31834 = teq env t1 t2  in
        force_trivial_guard env uu____31834
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31853 = teq_nosmt env t1 t2  in
        match uu____31853 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4382_31872 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4382_31872.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4382_31872.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4382_31872.FStar_TypeChecker_Common.implicits)
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
        (let uu____31908 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31908
         then
           let uu____31913 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31915 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31913
             uu____31915
         else ());
        (let uu____31920 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31920 with
         | (prob,x,wl) ->
             let g =
               let uu____31939 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31948  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31939  in
             ((let uu____31966 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31966
               then
                 let uu____31971 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31973 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31975 =
                   let uu____31977 = FStar_Util.must g  in
                   guard_to_string env uu____31977  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31971 uu____31973 uu____31975
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
        let uu____32014 = check_subtyping env t1 t2  in
        match uu____32014 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32033 =
              let uu____32034 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32034 g  in
            FStar_Pervasives_Native.Some uu____32033
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32053 = check_subtyping env t1 t2  in
        match uu____32053 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32072 =
              let uu____32073 =
                let uu____32074 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32074]  in
              FStar_TypeChecker_Env.close_guard env uu____32073 g  in
            FStar_Pervasives_Native.Some uu____32072
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32112 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32112
         then
           let uu____32117 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32119 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32117
             uu____32119
         else ());
        (let uu____32124 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32124 with
         | (prob,x,wl) ->
             let g =
               let uu____32139 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32148  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32139  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32169 =
                      let uu____32170 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32170]  in
                    FStar_TypeChecker_Env.close_guard env uu____32169 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32211 = subtype_nosmt env t1 t2  in
        match uu____32211 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  